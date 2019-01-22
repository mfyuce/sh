"""
http://amoffat.github.io/sh/
"""
# ===============================================================================
# Copyright (C) 2011-2017 by Andrew Moffat
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
# ===============================================================================


__version__ = "1.12.14"
__project_url__ = "https://github.com/amoffat/sh"

import platform

import sys

IS_PY3 = sys.version_info[0] == 3
MINOR_VER = sys.version_info[1]
IS_PY26 = sys.version_info[0] == 2 and MINOR_VER == 6

import traceback
import os
import re
from types import ModuleType
from functools import partial
import inspect
import stat
import glob as glob_module
import ast
from io import UnsupportedOperation

from locale import getpreferredencoding
import subprocess

DEFAULT_ENCODING = getpreferredencoding() or "UTF-8"

# normally i would hate this idea of using a global to signify whether we are
# running tests, because it breaks the assumption that what is running in the
# tests is what will run live, but we ONLY use this in a place that has no
# serious side-effects that could change anything.  as long as we do that, it
# should be ok
RUNNING_TESTS = bool(int(os.environ.get("SH_TESTS_RUNNING", "0")))
FORCE_USE_SELECT = bool(int(os.environ.get("SH_TESTS_USE_SELECT", "0")))

if IS_PY3:
    from io import StringIO

    ioStringIO = StringIO
    from io import BytesIO as cStringIO

    iocStringIO = cStringIO
    from queue import Queue, Empty

    # for some reason, python 3.1 removed the builtin "callable", wtf
    if not hasattr(__builtins__, "callable"):
        def callable(ob):
            return hasattr(ob, "__call__")
else:
    from StringIO import StringIO
    from cStringIO import OutputType as cStringIO
    from io import StringIO as ioStringIO
    from io import BytesIO as iocStringIO
    from Queue import Queue, Empty

IS_OSX = platform.system() == "Darwin"
IS_FreeBSD = platform.system() == "FreeBSD"
THIS_DIR = os.path.dirname(os.path.realpath(__file__))
SH_LOGGER_NAME = __name__
# used in redirecting
STDOUT = -1
STDERR = -2

import errno
# import termios
import signal
import select
import threading
# import fcntl
# import struct
import logging
import weakref

# a re-entrant lock for pushd.  this way, multiple threads that happen to use
# pushd will all see the current working directory for the duration of the
# with-context
PUSHD_LOCK = threading.RLock()

if hasattr(inspect, "getfullargspec"):
    def get_num_args(fn):
        return len(inspect.getfullargspec(fn).args)
else:
    def get_num_args(fn):
        return len(inspect.getargspec(fn).args)

if IS_PY3:
    raw_input = input
    unicode = str
    basestring = str
    long = int

_unicode_methods = set(dir(unicode()))

HAS_POLL = hasattr(select, "poll")
POLLER_EVENT_READ = 1
POLLER_EVENT_WRITE = 2
POLLER_EVENT_HUP = 4
POLLER_EVENT_ERROR = 8


def encode_to_py3bytes_or_py2str(s):
    """ takes anything and attempts to return a py2 string or py3 bytes.  this
    is typically used when creating command + arguments to be executed via
    os.exec* """

    fallback_encoding = "utf8"

    if IS_PY3:
        # if we're already bytes, do nothing
        if isinstance(s, bytes):
            pass
        else:
            s = str(s)
            try:
                s = bytes(s, DEFAULT_ENCODING)
            except UnicodeEncodeError:
                s = bytes(s, fallback_encoding)
    else:
        # attempt to convert the thing to unicode from the system's encoding
        try:
            s = unicode(s, DEFAULT_ENCODING)
        # if the thing is already unicode, or it's a number, it can't be
        # coerced to unicode with an encoding argument, but if we leave out
        # the encoding argument, it will convert it to a string, then to unicode
        except TypeError:
            s = unicode(s)

        # now that we have guaranteed unicode, encode to our system encoding,
        # but attempt to fall back to something
        try:
            s = s.encode(DEFAULT_ENCODING)
        except:
            s = s.encode(fallback_encoding, "replace")
    return s


def _indent_text(text, num=4):
    lines = []
    for line in text.split("\n"):
        line = (" " * num) + line
        lines.append(line)
    return "\n".join(lines)


class ForkException(Exception):
    def __init__(self, orig_exc):
        tmpl = """

Original exception:
===================

%s
"""
        msg = tmpl % _indent_text(orig_exc)
        Exception.__init__(self, msg)


class ErrorReturnCodeMeta(type):
    """ a metaclass which provides the ability for an ErrorReturnCode (or
    derived) instance, imported from one sh module, to be considered the
    subclass of ErrorReturnCode from another module.  this is mostly necessary
    in the tests, where we do assertRaises, but the ErrorReturnCode that the
    program we're testing throws may not be the same class that we pass to
    assertRaises
    """

    def __subclasscheck__(self, o):
        other_bases = set([b.__name__ for b in o.__bases__])
        return self.__name__ in other_bases or o.__name__ == self.__name__


class ErrorReturnCode(Exception):
    __metaclass__ = ErrorReturnCodeMeta

    """ base class for all exceptions as a result of a command's exit status
    being deemed an error.  this base class is dynamically subclassed into
    derived classes with the format: ErrorReturnCode_NNN where NNN is the exit
    code number.  the reason for this is it reduces boiler plate code when
    testing error return codes:
    
        try:
            some_cmd()
        except ErrorReturnCode_12:
            print("couldn't do X")
            
    vs:
        try:
            some_cmd()
        except ErrorReturnCode as e:
            if e.exit_code == 12:
                print("couldn't do X")
    
    it's not much of a savings, but i believe it makes the code easier to read """

    truncate_cap = 750

    def __init__(self, full_cmd, stdout, stderr, truncate=True):
        self.full_cmd = full_cmd
        self.stdout = stdout
        self.stderr = stderr

        exc_stdout = self.stdout
        if truncate:
            exc_stdout = exc_stdout[:self.truncate_cap]
            out_delta = len(self.stdout) - len(exc_stdout)
            if out_delta:
                exc_stdout += ("... (%d more, please see e.stdout)" % out_delta).encode()

        exc_stderr = self.stderr
        if truncate:
            exc_stderr = exc_stderr[:self.truncate_cap]
            err_delta = len(self.stderr) - len(exc_stderr)
            if err_delta:
                exc_stderr += ("... (%d more, please see e.stderr)" % err_delta).encode()

        msg_tmpl = unicode("\n\n  RAN: {cmd}\n\n  STDOUT:\n{stdout}\n\n  STDERR:\n{stderr}")

        msg = msg_tmpl.format(
            cmd=self.full_cmd,
            stdout=exc_stdout.decode(DEFAULT_ENCODING, "replace"),
            stderr=exc_stderr.decode(DEFAULT_ENCODING, "replace")
        )

        super(ErrorReturnCode, self).__init__(msg)


class SignalException(ErrorReturnCode): pass


class TimeoutException(Exception):
    """ the exception thrown when a command is killed because a specified
    timeout (via _timeout) was hit """

    def __init__(self, exit_code):
        self.exit_code = exit_code
        super(Exception, self).__init__()


SIGNALS_THAT_SHOULD_THROW_EXCEPTION = set((
    signal.SIGABRT,
    # signal.SIGBUS,
    signal.SIGFPE,
    signal.SIGILL,
    signal.SIGINT,
    # signal.SIGKILL,
    # signal.SIGPIPE,
    # signal.SIGQUIT,
    signal.SIGSEGV,
    signal.SIGTERM,
    # signal.SIGSYS,
))


# we subclass AttributeError because:
# https://github.com/ipython/ipython/issues/2577
# https://github.com/amoffat/sh/issues/97#issuecomment-10610629
class CommandNotFound(AttributeError): pass


rc_exc_regex = re.compile("(ErrorReturnCode|SignalException)_((\d+)|SIG[a-zA-Z]+)")
rc_exc_cache = {}

SIGNAL_MAPPING = {}
for k, v in signal.__dict__.items():
    if re.match(r"SIG[a-zA-Z]+", k):
        SIGNAL_MAPPING[v] = k


def get_exc_from_name(name):
    """ takes an exception name, like:

        ErrorReturnCode_1
        SignalException_9
        SignalException_SIGHUP

    and returns the corresponding exception.  this is primarily used for
    importing exceptions from sh into user code, for instance, to capture those
    exceptions """

    exc = None
    try:
        return rc_exc_cache[name]
    except KeyError:
        m = rc_exc_regex.match(name)
        if m:
            base = m.group(1)
            rc_or_sig_name = m.group(2)

            if base == "SignalException":
                try:
                    rc = -int(rc_or_sig_name)
                except ValueError:
                    rc = -getattr(signal, rc_or_sig_name)
            else:
                rc = int(rc_or_sig_name)

            exc = get_rc_exc(rc)
    return exc


def get_rc_exc(rc):
    """ takes a exit code or negative signal number and produces an exception
    that corresponds to that return code.  positive return codes yield
    ErrorReturnCode exception, negative return codes yield SignalException

    we also cache the generated exception so that only one signal of that type
    exists, preserving identity """

    try:
        return rc_exc_cache[rc]
    except KeyError:
        pass

    if rc > 0:
        name = "ErrorReturnCode_%d" % rc
        base = ErrorReturnCode
    else:
        signame = SIGNAL_MAPPING[abs(rc)]
        name = "SignalException_" + signame
        base = SignalException

    exc = ErrorReturnCodeMeta(name, (base,), {"exit_code": rc})
    rc_exc_cache[rc] = exc
    return exc


# we monkey patch glob.  i'm normally generally against monkey patching, but i
# decided to do this really un-intrusive patch because we need a way to detect
# if a list that we pass into an sh command was generated from glob.  the reason
# being that glob returns an empty list if a pattern is not found, and so
# commands will treat the empty list as no arguments, which can be a problem,
# ie:
#
#   ls(glob("*.ojfawe"))
#
# ^ will show the contents of your home directory, because it's essentially
# running ls([]) which, as a process, is just "ls".
#
# so we subclass list and monkey patch the glob function.  nobody should be the
# wiser, but we'll have results that we can make some determinations on
_old_glob = glob_module.glob


class GlobResults(list):
    def __init__(self, path, results):
        self.path = path
        list.__init__(self, results)


def glob(path, *args, **kwargs):
    expanded = GlobResults(path, _old_glob(path, *args, **kwargs))
    return expanded


glob_module.glob = glob


def which(program, paths=None):
    """ takes a program name or full path, plus an optional collection of search
    paths, and returns the full path of the requested executable.  if paths is
    specified, it is the entire list of search paths, and the PATH env is not
    used at all.  otherwise, PATH env is used to look for the program """

    def is_exe(fpath):
        return (os.path.exists(fpath) and
                os.access(fpath, os.X_OK) and
                os.path.isfile(os.path.realpath(fpath)))

    found_path = None
    fpath, fname = os.path.split(program)

    # if there's a path component, then we've specified a path to the program,
    # and we should just test if that program is executable.  if it is, return
    if fpath:
        program = os.path.abspath(os.path.expanduser(program))
        if is_exe(program):
            found_path = program

    # otherwise, we've just passed in the program name, and we need to search
    # the paths to find where it actually lives
    else:
        paths_to_search = []

        if isinstance(paths, (tuple, list)):
            paths_to_search.extend(paths)
        else:
            env_paths = os.environ.get("PATH", "").split(os.pathsep)
            paths_to_search.extend(env_paths)

        for path in paths_to_search:
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                found_path = exe_file
                break
            exe_file = exe_file + ".exe"
            if is_exe(exe_file):
                found_path = exe_file
                break

    return found_path


def resolve_command_path(program):
    path = which(program)
    if not path:
        # our actual command might have a dash in it, but we can't call
        # that from python (we have to use underscores), so we'll check
        # if a dash version of our underscore command exists and use that
        # if it does
        if "_" in program:
            path = which(program.replace("_", "-"))
        if not path:
            return None
    return path


def resolve_command(name, baked_args=None):
    path = resolve_command_path(name)
    cmd = None
    if path:
        cmd = Command(path)
        if baked_args:
            cmd = cmd.bake(**baked_args)
    return cmd


class Logger(object):
    """ provides a memory-inexpensive logger.  a gotcha about python's builtin
    logger is that logger objects are never garbage collected.  if you create a
    thousand loggers with unique names, they'll sit there in memory until your
    script is done.  with sh, it's easy to create loggers with unique names if
    we want our loggers to include our command arguments.  for example, these
    are all unique loggers:

            ls -l
            ls -l /tmp
            ls /tmp

    so instead of creating unique loggers, and without sacrificing logging
    output, we use this class, which maintains as part of its state, the logging
    "context", which will be the very unique name.  this allows us to get a
    logger with a very general name, eg: "command", and have a unique name
    appended to it via the context, eg: "ls -l /tmp" """

    def __init__(self, name, context=None):
        self.name = name
        self.log = logging.getLogger("%s.%s" % (SH_LOGGER_NAME, name))
        self.set_context(context)

    def _format_msg(self, msg, *args):
        if self.context:
            msg = "%s: %s" % (self.context, msg)
        return msg % args

    def set_context(self, context):
        if context:
            context = context.replace("%", "%%")
        self.context = context or ""

    def get_child(self, name, context):
        new_name = self.name + "." + name
        new_context = self.context + "." + context
        l = Logger(new_name, new_context)
        return l

    def info(self, msg, *args):
        self.log.info(self._format_msg(msg, *args))

    def debug(self, msg, *args):
        self.log.debug(self._format_msg(msg, *args))

    def error(self, msg, *args):
        self.log.error(self._format_msg(msg, *args))

    def exception(self, msg, *args):
        self.log.exception(self._format_msg(msg, *args))


def default_logger_str(cmd, call_args, pid=None):
    if pid:
        s = "<Command %r, pid %d>" % (cmd, pid)
    else:
        s = "<Command %r>" % cmd
    return s


class RunningCommand(object):
    """ this represents an executing Command object.  it is returned as the
    result of __call__() being executed on a Command instance.  this creates a
    reference to a OProc instance, which is a low-level wrapper around the
    process that was exec'd

    this is the class that gets manipulated the most by user code, and so it
    implements various convenience methods and logical mechanisms for the
    underlying process.  for example, if a user tries to access a
    backgrounded-process's stdout/err, the RunningCommand object is smart enough
    to know to wait() on the process to finish first.  and when the process
    finishes, RunningCommand is smart enough to translate exit codes to
    exceptions. """

    # these are attributes that we allow to passthrough to OProc for
    _OProc_attr_whitelist = set((
        "signal",
        "terminate",
        "kill",
        "kill_group",
        "signal_group",
        "pid",
        "sid",
        "pgid",
        "ctty",

        "input_thread_exc",
        "output_thread_exc",
        "bg_thread_exc",
    ))

    def __init__(self, cmd, call_args, stdin, stdout, stderr):
        """
            cmd is an array, where each element is encoded as bytes (PY3) or str
            (PY2)
        """

        # self.ran is used for auditing what actually ran.  for example, in
        # exceptions, or if you just want to know what was ran after the
        # command ran
        #
        # here we're making a consistent unicode string out if our cmd.
        # we're also assuming (correctly, i think) that the command and its
        # arguments are the encoding we pass into _encoding, which falls back to
        # the system's encoding
        enc = call_args["encoding"]
        self.ran = " ".join([arg.decode(enc, "ignore") for arg in cmd])

        self.call_args = call_args
        self.cmd = cmd

        self.process = None
        self._process_completed = False
        should_wait = True
        spawn_process = True

        # this is used to track if we've already raised StopIteration, and if we
        # have, raise it immediately again if the user tries to call next() on
        # us.  https://github.com/amoffat/sh/issues/273
        self._stopped_iteration = False

        # with contexts shouldn't run at all yet, they prepend
        # to every command in the context
        if call_args["with"]:
            spawn_process = False
            get_prepend_stack().append(self)

        if call_args["piped"] or call_args["iter"] or call_args["iter_noblock"]:
            should_wait = False

        # we're running in the background, return self and let us lazily
        # evaluate
        if call_args["bg"]:
            should_wait = False

        # redirection
        if call_args["err_to_out"]:
            stderr = STDOUT

        done_callback = call_args["done"]
        if done_callback:
            call_args["done"] = partial(done_callback, self)

            # set up which stream should write to the pipe
        # TODO, make pipe None by default and limit the size of the Queue
        # in oproc.OProc
        pipe = STDOUT
        if call_args["iter"] == "out" or call_args["iter"] is True:
            pipe = STDOUT
        elif call_args["iter"] == "err":
            pipe = STDERR

        if call_args["iter_noblock"] == "out" or call_args["iter_noblock"] is True:
            pipe = STDOUT
        elif call_args["iter_noblock"] == "err":
            pipe = STDERR

        # there's currently only one case where we wouldn't spawn a child
        # process, and that's if we're using a with-context with our command
        self._spawned_and_waited = False
        if spawn_process:
            log_str_factory = call_args["log_msg"] or default_logger_str
            logger_str = log_str_factory(self.ran, call_args)
            self.log = Logger("command", logger_str)

            self.log.info("starting process")

            if should_wait:
                self._spawned_and_waited = True

            # this lock is needed because of a race condition where a background
            # thread, created in the OProc constructor, may try to access
            # self.process, but it has not been assigned yet
            # process_assign_lock = threading.Lock()
            # with process_assign_lock:
            #     self.process = OProc(self, self.log, cmd, stdin, stdout, stderr,
            #                          self.call_args, pipe, process_assign_lock)
            self.output = subprocess.check_output('"' + cmd[0].decode() + '" ' + " " + " ".join([x.decode() for x in cmd[1:]]),
                                                  shell=True, stderr=subprocess.STDOUT)
            logger_str = log_str_factory(self.ran, call_args, "")  # self.process.pid
            self.log.set_context(logger_str)
            self.log.info("process started")

            # if should_wait:
            #     self.wait()

    def wait(self):
        """ waits for the running command to finish.  this is called on all
        running commands, eventually, except for ones that run in the background
        """
        if not self._process_completed:
            self._process_completed = True

            exit_code = self.process.wait()
            if self.process.timed_out:
                # if we timed out, our exit code represents a signal, which is
                # negative, so let's make it positive to store in our
                # TimeoutException
                raise TimeoutException(-exit_code)

            else:
                self.handle_command_exit_code(exit_code)

                # if an iterable command is using an instance of OProc for its stdin,
                # wait on it.  the process is probably set to "piped", which means it
                # won't be waited on, which means exceptions won't propagate up to the
                # main thread.  this allows them to bubble up
                if self.process._stdin_process:
                    self.process._stdin_process.command.wait()

        self.log.info("process completed")
        return self

    def handle_command_exit_code(self, code):
        """ here we determine if we had an exception, or an error code that we
        weren't expecting to see.  if we did, we create and raise an exception
        """
        ca = self.call_args
        exc_class = get_exc_exit_code_would_raise(code, ca["ok_code"],
                                                  ca["piped"])
        if exc_class:
            exc = exc_class(self.ran, self.process.stdout, self.process.stderr,
                            ca["truncate_exc"])
            raise exc

    @property
    def stdout(self):
        self.wait()
        return self.process.stdout

    @property
    def stderr(self):
        self.wait()
        return self.process.stderr

    @property
    def exit_code(self):
        self.wait()
        return self.process.exit_code

    def __len__(self):
        return len(str(self))

    def __enter__(self):
        """ we don't actually do anything here because anything that should have
        been done would have been done in the Command.__call__ call.
        essentially all that has to happen is the comand be pushed on the
        prepend stack. """
        pass

    def __iter__(self):
        return self

    def next(self):
        """ allow us to iterate over the output of our command """

        if self._stopped_iteration:
            raise StopIteration()

        # we do this because if get blocks, we can't catch a KeyboardInterrupt
        # so the slight timeout allows for that.
        while True:
            try:
                chunk = self.process._pipe_queue.get(True, 0.001)
            except Empty:
                if self.call_args["iter_noblock"]:
                    return errno.EWOULDBLOCK
            else:
                if chunk is None:
                    self.wait()
                    self._stopped_iteration = True
                    raise StopIteration()
                try:
                    return chunk.decode(self.call_args["encoding"],
                                        self.call_args["decode_errors"])
                except UnicodeDecodeError:
                    return chunk

    # python 3
    __next__ = next

    def __exit__(self, typ, value, traceback):
        if self.call_args["with"] and get_prepend_stack():
            get_prepend_stack().pop()

    def __str__(self):
        """ in python3, should return unicode.  in python2, should return a
        string of bytes """
        if IS_PY3:
            return self.__unicode__()
        else:
            return unicode(self).encode(self.call_args["encoding"])

    def __unicode__(self):
        """ a magic method defined for python2.  calling unicode() on a
        RunningCommand object will call this """
        if self.process and self.stdout:
            return self.stdout.decode(self.call_args["encoding"],
                                      self.call_args["decode_errors"])
        if self.output:
            return self.output.decode(self.call_args["encoding"],
                                      self.call_args["decode_errors"])
        elif IS_PY3:
            return ""
        else:
            return unicode("")

    def __eq__(self, other):
        return unicode(self) == unicode(other)

    __hash__ = None  # Avoid DeprecationWarning in Python < 3

    def __contains__(self, item):
        return item in str(self)

    def __getattr__(self, p):
        # let these three attributes pass through to the OProc object
        if p in self._OProc_attr_whitelist:
            if self.process:
                return getattr(self.process, p)
            else:
                raise AttributeError

        # see if strings have what we're looking for.  we're looking at the
        # method names explicitly because we don't want to evaluate self unless
        # we absolutely have to, the reason being, in python2, hasattr swallows
        # exceptions, and if we try to run hasattr on a command that failed and
        # is being run with _iter=True, the command will be evaluated, throw an
        # exception, but hasattr will discard it
        if p in _unicode_methods:
            return getattr(unicode(self), p)

        raise AttributeError

    def __repr__(self):
        """ in python3, should return unicode.  in python2, should return a
        string of bytes """
        try:
            return str(self)
        except UnicodeDecodeError:
            if self.process:
                if self.stdout:
                    return repr(self.stdout)
            return repr("")

    def __long__(self):
        return long(str(self).strip())

    def __float__(self):
        return float(str(self).strip())

    def __int__(self):
        return int(str(self).strip())


def output_redirect_is_filename(out):
    return isinstance(out, basestring)


def get_prepend_stack():
    tl = Command.thread_local
    if not hasattr(tl, "_prepend_stack"):
        tl._prepend_stack = []
    return tl._prepend_stack


def special_kwarg_validator(kwargs, invalid_list):
    s1 = set(kwargs.keys())
    invalid_args = []

    for args in invalid_list:

        if callable(args):
            fn = args
            ret = fn(kwargs)
            invalid_args.extend(ret)

        else:
            args, error_msg = args

            if s1.issuperset(args):
                invalid_args.append((args, error_msg))

    return invalid_args


def get_fileno(ob):
    # in py2, this will return None.  in py3, it will return an method that
    # raises when called
    fileno_meth = getattr(ob, "fileno", None)

    fileno = None
    if fileno_meth:
        # py3 StringIO objects will report a fileno, but calling it will raise
        # an exception
        try:
            fileno = fileno_meth()
        except UnsupportedOperation:
            pass
    elif isinstance(ob, (int, long)) and ob >= 0:
        fileno = ob

    return fileno


def ob_is_tty(ob):
    """ checks if an object (like a file-like object) is a tty.  """
    fileno = get_fileno(ob)
    is_tty = False
    if fileno:
        is_tty = os.isatty(fileno)
    return is_tty


def ob_is_pipe(ob):
    fileno = get_fileno(ob)
    is_pipe = False
    if fileno:
        fd_stat = os.fstat(fileno)
        is_pipe = stat.S_ISFIFO(fd_stat.st_mode)
    return is_pipe


def tty_in_validator(kwargs):
    pairs = (("tty_in", "in"), ("tty_out", "out"))
    invalid = []
    for tty, std in pairs:
        if tty in kwargs and ob_is_tty(kwargs.get(std, None)):
            args = (tty, std)
            error = "`_%s` is a TTY already, so so it doesn't make sense \
to set up a TTY with `_%s`" % (std, tty)
            invalid.append((args, error))

    return invalid


def bufsize_validator(kwargs):
    """ a validator to prevent a user from saying that they want custom
    buffering when they're using an in/out object that will be os.dup'd to the
    process, and has its own buffering.  an example is a pipe or a tty.  it
    doesn't make sense to tell them to have a custom buffering, since the os
    controls this. """
    invalid = []

    in_ob = kwargs.get("in", None)
    out_ob = kwargs.get("out", None)

    in_buf = kwargs.get("in_bufsize", None)
    out_buf = kwargs.get("out_bufsize", None)

    in_no_buf = ob_is_tty(in_ob) or ob_is_pipe(in_ob)
    out_no_buf = ob_is_tty(out_ob) or ob_is_pipe(out_ob)

    err = "Can't specify an {target} bufsize if the {target} target is a pipe or TTY"

    if in_no_buf and in_buf is not None:
        invalid.append((("in", "in_bufsize"), err.format(target="in")))

    if out_no_buf and out_buf is not None:
        invalid.append((("out", "out_bufsize"), err.format(target="out")))

    return invalid


class Command(object):
    """ represents an un-run system program, like "ls" or "cd".  because it
    represents the program itself (and not a running instance of it), it should
    hold very little state.  in fact, the only state it does hold is baked
    arguments.

    when a Command object is called, the result that is returned is a
    RunningCommand object, which represents the Command put into an execution
    state. """
    thread_local = threading.local()

    _call_args = {
        "fg": False,  # run command in foreground

        # run a command in the background.  commands run in the background
        # ignore SIGHUP and do not automatically exit when the parent process
        # ends
        "bg": False,

        # automatically report exceptions for background commands
        "bg_exc": True,

        "with": False,  # prepend the command to every command after it
        "in": None,
        "out": None,  # redirect STDOUT
        "err": None,  # redirect STDERR
        "err_to_out": None,  # redirect STDERR to STDOUT

        # stdin buffer size
        # 1 for line, 0 for unbuffered, any other number for that amount
        "in_bufsize": 0,
        # stdout buffer size, same values as above
        "out_bufsize": 1,
        "err_bufsize": 1,

        # this is how big the output buffers will be for stdout and stderr.
        # this is essentially how much output they will store from the process.
        # we use a deque, so if it overflows past this amount, the first items
        # get pushed off as each new item gets added.
        #
        # NOTICE
        # this is not a *BYTE* size, this is a *CHUNK* size...meaning, that if
        # you're buffering out/err at 1024 bytes, the internal buffer size will
        # be "internal_bufsize" CHUNKS of 1024 bytes
        "internal_bufsize": 3 * 1024 ** 2,

        "env": None,
        "piped": None,
        "iter": None,
        "iter_noblock": None,
        "ok_code": 0,
        "cwd": None,

        # the separator delimiting between a long-argument's name and its value
        # setting this to None will cause name and value to be two separate
        # arguments, like for short options
        # for example, --arg=derp, '=' is the long_sep
        "long_sep": "=",

        # the prefix used for long arguments
        "long_prefix": "--",

        # this is for programs that expect their input to be from a terminal.
        # ssh is one of those programs
        "tty_in": False,
        "tty_out": True,

        "encoding": DEFAULT_ENCODING,
        "decode_errors": "strict",

        # how long the process should run before it is auto-killed
        "timeout": None,
        "timeout_signal": signal.SIGTERM,  # SIGKILL,

        # TODO write some docs on "long-running processes"
        # these control whether or not stdout/err will get aggregated together
        # as the process runs.  this has memory usage implications, so sometimes
        # with long-running processes with a lot of data, it makes sense to
        # set these to true
        "no_out": False,
        "no_err": False,
        "no_pipe": False,

        # if any redirection is used for stdout or stderr, internal buffering
        # of that data is not stored.  this forces it to be stored, as if
        # the output is being T'd to both the redirected destination and our
        # internal buffers
        "tee": None,

        # will be called when a process terminates regardless of exception
        "done": None,

        # a tuple (rows, columns) of the desired size of both the stdout and
        # stdin ttys, if ttys are being used
        "tty_size": (20, 80),

        # whether or not our exceptions should be truncated
        "truncate_exc": True,

        # a function to call after the child forks but before the process execs
        "preexec_fn": None,

        # UID to set after forking. Requires root privileges. Not supported on
        # Windows.
        "uid": None,

        # put the forked process in its own process session?
        "new_session": True,

        # pre-process args passed into __call__.  only really useful when used
        # in .bake()
        "arg_preprocess": None,

        # a callable that produces a log message from an argument tuple of the
        # command and the args
        "log_msg": None,
    }

    # this is a collection of validators to make sure the special kwargs make
    # sense
    _kwarg_validators = (
        (("fg", "bg"), "Command can't be run in the foreground and background"),
        (("fg", "err_to_out"), "Can't redirect STDERR in foreground mode"),
        (("err", "err_to_out"), "Stderr is already being redirected"),
        (("piped", "iter"), "You cannot iterate when this command is being piped"),
        (("piped", "no_pipe"), "Using a pipe doesn't make sense if you've \
disabled the pipe"),
        (("no_out", "iter"), "You cannot iterate over output if there is no \
output"),
        tty_in_validator,
        bufsize_validator,
    )

    def __init__(self, path, search_paths=None):
        found = which(path, search_paths)

        self._path = encode_to_py3bytes_or_py2str("")

        # is the command baked (aka, partially applied)?
        self._partial = False
        self._partial_baked_args = []
        self._partial_call_args = {}

        # bugfix for functools.wraps.  issue #121
        self.__name__ = str(self)

        if not found:
            raise CommandNotFound(path)

        # the reason why we set the values early in the constructor, and again
        # here, is for people who have tools that inspect the stack on
        # exception.  if CommandNotFound is raised, we need self._path and the
        # other attributes to be set correctly, so repr() works when they're
        # inspecting the stack.  issue #304
        self._path = encode_to_py3bytes_or_py2str(found)
        self.__name__ = str(self)

    def __getattribute__(self, name):
        # convenience
        getattr = partial(object.__getattribute__, self)
        val = None

        if name.startswith("_"):
            val = getattr(name)

        elif name == "bake":
            val = getattr("bake")

        # here we have a way of getting past shadowed subcommands.  for example,
        # if "git bake" was a thing, we wouldn't be able to do `git.bake()`
        # because `.bake()` is already a method.  so we allow `git.bake_()`
        elif name.endswith("_"):
            name = name[:-1]

        if val is None:
            val = getattr("bake")(name)

        return val

    @staticmethod
    def _extract_call_args(kwargs):
        """ takes kwargs that were passed to a command's __call__ and extracts
        out the special keyword arguments, we return a tuple of special keyword
        args, and kwargs that will go to the execd command """

        kwargs = kwargs.copy()
        call_args = {}
        for parg, default in Command._call_args.items():
            key = "_" + parg

            if key in kwargs:
                call_args[parg] = kwargs[key]
                del kwargs[key]

        invalid_kwargs = special_kwarg_validator(call_args,
                                                 Command._kwarg_validators)

        if invalid_kwargs:
            exc_msg = []
            for args, error_msg in invalid_kwargs:
                exc_msg.append("  %r: %s" % (args, error_msg))
            exc_msg = "\n".join(exc_msg)
            raise TypeError("Invalid special arguments:\n\n%s\n" % exc_msg)

        return call_args, kwargs

    # TODO needs documentation
    def bake(self, *args, **kwargs):
        fn = type(self)(self._path)
        fn._partial = True

        call_args, kwargs = self._extract_call_args(kwargs)

        pruned_call_args = call_args
        for k, v in Command._call_args.items():
            try:
                if pruned_call_args[k] == v:
                    del pruned_call_args[k]
            except KeyError:
                continue

        fn._partial_call_args.update(self._partial_call_args)
        fn._partial_call_args.update(pruned_call_args)
        fn._partial_baked_args.extend(self._partial_baked_args)
        sep = pruned_call_args.get("long_sep", self._call_args["long_sep"])
        prefix = pruned_call_args.get("long_prefix",
                                      self._call_args["long_prefix"])
        fn._partial_baked_args.extend(compile_args(args, kwargs, sep, prefix))
        return fn

    def __str__(self):
        """ in python3, should return unicode.  in python2, should return a
        string of bytes """
        if IS_PY3:
            return self.__unicode__()
        else:
            return self.__unicode__().encode(DEFAULT_ENCODING)

    def __eq__(self, other):
        return str(self) == str(other)

    __hash__ = None  # Avoid DeprecationWarning in Python < 3

    def __repr__(self):
        """ in python3, should return unicode.  in python2, should return a
        string of bytes """
        return "<Command %r>" % str(self)

    def __unicode__(self):
        """ a magic method defined for python2.  calling unicode() on a
        self will call this """
        baked_args = " ".join(item.decode(DEFAULT_ENCODING) for item in self._partial_baked_args)
        if baked_args:
            baked_args = " " + baked_args
        return self._path.decode(DEFAULT_ENCODING) + baked_args

    def __enter__(self):
        self(_with=True)

    def __exit__(self, typ, value, traceback):
        get_prepend_stack().pop()

    def __call__(self, *args, **kwargs):

        kwargs = kwargs.copy()
        args = list(args)

        # this will hold our final command, including arguments, that will be
        # execd
        cmd = []

        # this will hold a complete mapping of all our special keyword arguments
        # and their values
        call_args = Command._call_args.copy()

        # aggregate any 'with' contexts
        for prepend in get_prepend_stack():
            pcall_args = prepend.call_args.copy()
            # don't pass the 'with' call arg
            pcall_args.pop("with", None)

            call_args.update(pcall_args)
            cmd.extend(prepend.cmd)

        cmd.append(self._path)

        # do we have an argument pre-processor?  if so, run it.  we need to do
        # this early, so that args, kwargs are accurate
        preprocessor = self._partial_call_args.get("arg_preprocess", None)
        if preprocessor:
            args, kwargs = preprocessor(args, kwargs)

        # here we extract the special kwargs and override any
        # special kwargs from the possibly baked command
        extracted_call_args, kwargs = self._extract_call_args(kwargs)

        call_args.update(self._partial_call_args)
        call_args.update(extracted_call_args)

        # handle a None.  this is added back only to not break the api in the
        # 1.* version.  TODO remove this in 2.0, as "ok_code", if specified,
        # should always be a definitive value or list of values, and None is
        # ambiguous
        if call_args["ok_code"] is None:
            call_args["ok_code"] = 0

        if not getattr(call_args["ok_code"], "__iter__", None):
            call_args["ok_code"] = [call_args["ok_code"]]

        # check if we're piping via composition
        stdin = call_args["in"]
        if args:
            first_arg = args.pop(0)
            if isinstance(first_arg, RunningCommand):
                if first_arg.call_args["piped"]:
                    stdin = first_arg.process
                else:
                    stdin = first_arg.process._pipe_queue

            else:
                args.insert(0, first_arg)

        processed_args = compile_args(args, kwargs, call_args["long_sep"],
                                      call_args["long_prefix"])

        # makes sure our arguments are broken up correctly
        split_args = self._partial_baked_args + processed_args

        final_args = split_args

        cmd.extend(final_args)

        # if we're running in foreground mode, we need to completely bypass
        # launching a RunningCommand and OProc and just do a spawn
        if call_args["fg"]:
            if call_args["env"] is None:
                launch = lambda: os.spawnv(os.P_WAIT, cmd[0], cmd)
            else:
                launch = lambda: os.spawnve(os.P_WAIT, cmd[0], cmd, call_args["env"])

            exit_code = launch()
            exc_class = get_exc_exit_code_would_raise(exit_code,
                                                      call_args["ok_code"], call_args["piped"])
            if exc_class:
                if IS_PY3:
                    ran = " ".join([arg.decode(DEFAULT_ENCODING, "ignore") for arg in cmd])
                else:
                    ran = " ".join(cmd)
                exc = exc_class(ran, b"", b"", call_args["truncate_exc"])
                raise exc
            return None

        # stdout redirection
        stdout = call_args["out"]
        if output_redirect_is_filename(stdout):
            stdout = open(str(stdout), "wb")

        # stderr redirection
        stderr = call_args["err"]
        if output_redirect_is_filename(stderr):
            stderr = open(str(stderr), "wb")

        return RunningCommand(cmd, call_args, stdin, stdout, stderr)


def compile_args(args, kwargs, sep, prefix):
    """ takes args and kwargs, as they were passed into the command instance
    being executed with __call__, and compose them into a flat list that
    will eventually be fed into exec.  example:

    with this call:

        sh.ls("-l", "/tmp", color="never")

    this function receives

        args = ['-l', '/tmp']
        kwargs = {'color': 'never'}

    and produces

        ['-l', '/tmp', '--color=never']

    """
    processed_args = []
    encode = encode_to_py3bytes_or_py2str

    # aggregate positional args
    for arg in args:
        if isinstance(arg, (list, tuple)):
            if isinstance(arg, GlobResults) and not arg:
                arg = [arg.path]

            for sub_arg in arg:
                processed_args.append(encode(sub_arg))
        elif isinstance(arg, dict):
            processed_args += aggregate_keywords(arg, sep, prefix, raw=True)
        else:
            processed_args.append(encode(arg))

    # aggregate the keyword arguments
    processed_args += aggregate_keywords(kwargs, sep, prefix)

    return processed_args


def aggregate_keywords(keywords, sep, prefix, raw=False):
    """ take our keyword arguments, and a separator, and compose the list of
    flat long (and short) arguments.  example

        {'color': 'never', 't': True, 'something': True} with sep '='

    becomes

        ['--color=never', '-t', '--something']

    the `raw` argument indicates whether or not we should leave the argument
    name alone, or whether we should replace "_" with "-".  if we pass in a
    dictionary, like this:

        sh.command({"some_option": 12})

    then `raw` gets set to True, because we want to leave the key as-is, to
    produce:

        ['--some_option=12']

    but if we just use a command's kwargs, `raw` is False, which means this:

        sh.command(some_option=12)

    becomes:

        ['--some-option=12']

    eessentially, using kwargs is a convenience, but it lacks the ability to
    put a '-' in the name, so we do the replacement of '_' to '-' for you.
    but when you really don't want that to happen, you should use a
    dictionary instead with the exact names you want
    """

    processed = []
    encode = encode_to_py3bytes_or_py2str

    for k, v in keywords.items():
        # we're passing a short arg as a kwarg, example:
        # cut(d="\t")
        if len(k) == 1:
            if v is not False:
                processed.append(encode("-" + k))
                if v is not True:
                    processed.append(encode(v))

        # we're doing a long arg
        else:
            if not raw:
                k = k.replace("_", "-")

            if v is True:
                processed.append(encode("--" + k))
            elif v is False:
                pass
            elif sep is None or sep == " ":
                processed.append(encode(prefix + k))
                processed.append(encode(v))
            else:
                arg = encode("%s%s%s%s" % (prefix, k, sep, v))
                processed.append(arg)

    return processed


def _start_daemon_thread(fn, name, exc_queue, *args):
    def wrap(*args, **kwargs):
        try:
            fn(*args, **kwargs)
        except Exception as e:
            exc_queue.put(e)
            raise

    thrd = threading.Thread(target=wrap, name=name, args=args)
    thrd.daemon = True
    thrd.start()
    return thrd


#
# def setwinsize(fd, rows_cols):
#     """ set the terminal size of a tty file descriptor.  borrowed logic
#     from pexpect.py """
#     rows, cols = rows_cols
#     TIOCSWINSZ = getattr(termios, 'TIOCSWINSZ', -2146929561)
#
#     s = struct.pack('HHHH', rows, cols, 0, 0)
#     fcntl.ioctl(fd, TIOCSWINSZ, s)


def construct_streamreader_callback(process, handler):
    """ here we're constructing a closure for our streamreader callback.  this
    is used in the case that we pass a callback into _out or _err, meaning we
    want to our callback to handle each bit of output

    we construct the closure based on how many arguments it takes.  the reason
    for this is to make it as easy as possible for people to use, without
    limiting them.  a new user will assume the callback takes 1 argument (the
    data).  as they get more advanced, they may want to terminate the process,
    or pass some stdin back, and will realize that they can pass a callback of
    more args """

    # implied arg refers to the "self" that methods will pass in.  we need to
    # account for this implied arg when figuring out what function the user
    # passed in based on number of args
    implied_arg = 0

    partial_args = 0
    handler_to_inspect = handler

    if isinstance(handler, partial):
        partial_args = len(handler.args)
        handler_to_inspect = handler.func

    if inspect.ismethod(handler_to_inspect):
        implied_arg = 1
        num_args = get_num_args(handler_to_inspect)

    else:
        if inspect.isfunction(handler_to_inspect):
            num_args = get_num_args(handler_to_inspect)

        # is an object instance with __call__ method
        else:
            implied_arg = 1
            num_args = get_num_args(handler_to_inspect.__call__)

    net_args = num_args - implied_arg - partial_args

    handler_args = ()

    # just the chunk
    if net_args == 1:
        handler_args = ()

    # chunk, stdin
    if net_args == 2:
        handler_args = (process.stdin,)

    # chunk, stdin, process
    elif net_args == 3:
        # notice we're only storing a weakref, to prevent cyclic references
        # (where the process holds a streamreader, and a streamreader holds a
        # handler-closure with a reference to the process
        handler_args = (process.stdin, weakref.ref(process))

    def fn(chunk):
        # this is pretty ugly, but we're evaluating the process at call-time,
        # because it's a weakref
        args = handler_args
        if len(args) == 2:
            args = (handler_args[0], handler_args[1]())
        return handler(chunk, *args)

    return fn


def get_exc_exit_code_would_raise(exit_code, ok_codes, sigpipe_ok):
    exc = None
    success = exit_code in ok_codes
    bad_sig = -exit_code in SIGNALS_THAT_SHOULD_THROW_EXCEPTION

    # if this is a piped command, SIGPIPE must be ignored by us and not raise an
    # exception, since it's perfectly normal for the consumer of a process's
    # pipe to terminate early
    if sigpipe_ok and -exit_code == signal.SIGPIPE:
        bad_sig = False
        success = True

    if not success or bad_sig:
        exc = get_rc_exc(exit_code)
    return exc


def handle_process_exit_code(exit_code):
    """ this should only ever be called once for each child process """
    # if we exited from a signal, let our exit code reflect that
    if os.WIFSIGNALED(exit_code):
        exit_code = -os.WTERMSIG(exit_code)
    # otherwise just give us a normal exit code
    elif os.WIFEXITED(exit_code):
        exit_code = os.WEXITSTATUS(exit_code)
    else:
        raise RuntimeError("Unknown child exit status!")

    return exit_code


def no_interrupt(syscall, *args, **kwargs):
    """ a helper for making system calls immune to EINTR """
    ret = None

    while True:
        try:
            ret = syscall(*args, **kwargs)
        except OSError as e:
            if e.errno == errno.EINTR:
                continue
            else:
                raise
        else:
            break

    return ret


class Environment(dict):
    """ this allows lookups to names that aren't found in the global scope to be
    searched for as a program name.  for example, if "ls" isn't found in this
    module's scope, we consider it a system program and try to find it.

    we use a dict instead of just a regular object as the base class because the
    exec() statement used in the run_repl requires the "globals" argument to be a
    dictionary """

    # this is a list of all of the names that the sh module exports that will
    # not resolve to functions.  we don't want to accidentally shadow real
    # commands with functions/imports that we define in sh.py.  for example,
    # "import time" may override the time system program
    whitelist = set([
        "Command",
        "RunningCommand",
        "CommandNotFound",
        "DEFAULT_ENCODING",
        "DoneReadingForever",
        "ErrorReturnCode",
        "NotYetReadyToRead",
        "SignalException",
        "ForkException",
        "TimeoutException",
        "__project_url__",
        "__version__",
        "__file__",
        "args",
        "pushd",
        "glob",
        "contrib",
    ])

    def __init__(self, globs, baked_args={}):
        """ baked_args are defaults for the 'sh' execution context.  for
        example:

            tmp = sh(_out=StringIO())

        'out' would end up in here as an entry in the baked_args dict """

        self.globs = globs
        self.baked_args = baked_args
        self.disable_whitelist = False

    def __getitem__(self, k):
        # if we first import "_disable_whitelist" from sh, we can import
        # anything defined in the global scope of sh.py.  this is useful for our
        # tests
        if k == "_disable_whitelist":
            self.disable_whitelist = True
            return None

        # we're trying to import something real (maybe), see if it's in our
        # global scope
        if k in self.whitelist or self.disable_whitelist:
            return self.globs[k]

        # somebody tried to be funny and do "from sh import *"
        if k == "__all__":
            raise RuntimeError("Cannot import * from sh. \
Please import sh or import programs individually.")

        # check if we're naming a dynamically generated ReturnCode exception
        exc = get_exc_from_name(k)
        if exc:
            return exc

        # https://github.com/ipython/ipython/issues/2577
        # https://github.com/amoffat/sh/issues/97#issuecomment-10610629
        if k.startswith("__") and k.endswith("__"):
            raise AttributeError

        # is it a custom builtin?
        builtin = getattr(self, "b_" + k, None)
        if builtin:
            return builtin

        # is it a command?
        cmd = resolve_command(k, self.baked_args)
        if cmd:
            return cmd

        # how about an environment variable?
        # this check must come after testing if its a command, because on some
        # systems, there are an environment variables that can conflict with
        # command names.
        # https://github.com/amoffat/sh/issues/238
        try:
            return os.environ[k]
        except KeyError:
            pass

        # nothing found, raise an exception
        raise CommandNotFound(k)

    # methods that begin with "b_" are custom builtins and will override any
    # program that exists in our path.  this is useful for things like
    # common shell builtins that people are used to, but which aren't actually
    # full-fledged system binaries

    def b_cd(self, path=None):
        if path:
            os.chdir(path)
        else:
            os.chdir(os.path.expanduser('~'))

    def b_which(self, program, paths=None):
        return which(program, paths)


# this is a thin wrapper around THIS module (we patch sys.modules[__name__]).
# this is in the case that the user does a "from sh import whatever"
# in other words, they only want to import certain programs, not the whole
# system PATH worth of commands.  in this case, we just proxy the
# import lookup to our Environment class
class SelfWrapper(ModuleType):
    def __init__(self, self_module, baked_args={}):
        # this is super ugly to have to copy attributes like this,
        # but it seems to be the only way to make reload() behave
        # nicely.  if i make these attributes dynamic lookups in
        # __getattr__, reload sometimes chokes in weird ways...
        for attr in ["__builtins__", "__doc__", "__file__", "__name__", "__package__"]:
            setattr(self, attr, getattr(self_module, attr, None))

        # python 3.2 (2.7 and 3.3 work fine) breaks on osx (not ubuntu)
        # if we set this to None.  and 3.3 needs a value for __path__
        self.__path__ = []
        self.__self_module = self_module
        self.__env = Environment(globals(), baked_args=baked_args)

    def __getattr__(self, name):
        return self.__env[name]

    def __call__(self, **kwargs):
        """ returns a new SelfWrapper object, where all commands spawned from it
        have the baked_args kwargs set on them by default """
        baked_args = self.__env.baked_args.copy()
        baked_args.update(kwargs)
        new_mod = self.__class__(self.__self_module, baked_args)

        # inspect the line in the parent frame that calls and assigns the new sh
        # variable, and get the name of the new variable we're assigning to.
        # this is very brittle and pretty much a sin.  but it works in 99% of
        # the time and the tests pass
        #
        # the reason we need to do this is because we need to remove the old
        # cached module from sys.modules.  if we don't, it gets re-used, and any
        # old baked params get used, which is not what we want
        parent = inspect.stack()[1]
        code = parent[4][0].strip()
        parsed = ast.parse(code)
        module_name = parsed.body[0].targets[0].id

        if module_name == __name__:
            raise RuntimeError("Cannot use the name 'sh' as an execution context")

        sys.modules.pop(module_name, None)

        return new_mod


def in_importlib(frame):
    """ helper for checking if a filename is in importlib guts """
    return frame.f_code.co_filename == "<frozen importlib._bootstrap>"


def register_importer():
    """ registers our fancy importer that can let us import from a module name,
    like:

        import sh
        tmp = sh()
        from tmp import ls
    """

    def test(importer):
        return importer.__class__.__name__ == ModuleImporterFromVariables.__name__

    already_registered = any([True for i in sys.meta_path if test(i)])

    if not already_registered:
        importer = ModuleImporterFromVariables(
            restrict_to=["SelfWrapper"],
        )
        sys.meta_path.insert(0, importer)

    return not already_registered


def fetch_module_from_frame(name, frame):
    mod = frame.f_locals.get(name, frame.f_globals.get(name, None))
    return mod


class ModuleImporterFromVariables(object):
    """ a fancy importer that allows us to import from a variable that was
    recently set in either the local or global scope, like this:

        sh2 = sh(_timeout=3)
        from sh2 import ls

    """

    def __init__(self, restrict_to=None):
        self.restrict_to = set(restrict_to or set())

    def find_module(self, mod_fullname, path=None):
        """ mod_fullname doubles as the name of the VARIABLE holding our new sh
        context.  for example:

            derp = sh()
            from derp import ls

        here, mod_fullname will be "derp".  keep that in mind as we go throug
        the rest of this function """

        parent_frame = inspect.currentframe().f_back
        while in_importlib(parent_frame):
            parent_frame = parent_frame.f_back

        # this line is saying "hey, does mod_fullname exist as a name we've
        # defind previously?"  the purpose of this is to ensure that
        # mod_fullname is really a thing we've defined.  if we haven't defined
        # it before, then we "can't" import from it
        module = fetch_module_from_frame(mod_fullname, parent_frame)
        if not module:
            return None

        # make sure it's a class we're allowed to import from
        if module.__class__.__name__ not in self.restrict_to:
            return None

        return self

    def load_module(self, mod_fullname):
        parent_frame = inspect.currentframe().f_back

        while in_importlib(parent_frame):
            parent_frame = parent_frame.f_back

        module = fetch_module_from_frame(mod_fullname, parent_frame)

        # we HAVE to include the module in sys.modules, per the import PEP.
        # older verions of python were more lenient about this being set, but
        # not in >= python3.3, unfortunately.  this requirement necessitates the
        # ugly code in SelfWrapper.__call__
        sys.modules[mod_fullname] = module
        module.__loader__ = self

        return module


def run_repl(env):  # pragma: no cover
    banner = "\n>> sh v{version}\n>> https://github.com/amoffat/sh\n"

    print(banner.format(version=__version__))
    while True:
        try:
            line = raw_input("sh> ")
        except (ValueError, EOFError):
            break

        try:
            exec(compile(line, "<dummy>", "single"), env, env)
        except SystemExit:
            break
        except:
            print(traceback.format_exc())

    # cleans up our last line
    print("")


# we're being run as a stand-alone script
if __name__ == "__main__":  # pragma: no cover
    def parse_args():
        from optparse import OptionParser

        parser = OptionParser()
        parser.add_option("-e", "--envs", dest="envs", action="append")
        parser.add_option("-l", "--locales", dest="constrain_locales", action="append")
        options, args = parser.parse_args()

        envs = options.envs or []
        constrain_locales = options.constrain_locales or []

        return args, envs, constrain_locales


    # these are essentially restrictions on what envs/constrain_locales to restrict to for
    # the tests.  if they're empty lists, it means use all available
    args, constrain_versions, constrain_locales = parse_args()
    action = None
    if args:
        action = args[0]

    env = Environment(globals())
    run_repl(env)

# we're being imported from somewhere
else:
    self = sys.modules[__name__]
    sys.modules[__name__] = SelfWrapper(self)
    register_importer()
