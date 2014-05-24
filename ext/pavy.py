#!/usr/bin/env python

import sys
import os
import os.path
import atexit
import tempfile
import shutil
import subprocess as sub
import threading
import signal
import time


#
# globals ...
#
root = os.path.dirname (os.path.realpath (__file__))
verbose = True      # TODO: make an option
running = list()    # list of running processes

###############################################################################

def parseOpt (argv):
    from optparse import OptionParser
    
    parser = OptionParser ()
    parser.add_option ("--save-temps", dest="save_temps",
                       help="Do not delete temporary files",
                       action="store_true",
                       default=False)
    parser.add_option ("--temp-dir", dest="temp_dir",
                       help="Temporary directory",
                       default=None)
    # parser.add_option ('--cpu', type='int', dest='cpu',
    #                    help='CPU time limit (seconds) TEMP: has no effect', 
    #                    default=-1)
    # parser.add_option ('--mem', type='int', dest='mem',
    #                    help='MEM limit (MB) TEMP: has no effect', default=-1)

    (options, args) = parser.parse_args (argv)

    return (options, args)

def createWorkDir (dname = None, save = False):    
    if dname == None:
        workdir = tempfile.mkdtemp (prefix='avy-')
    else:
        workdir = dname
    if verbose: print "Working directory", workdir
    if not save: atexit.register (shutil.rmtree, path=workdir)
    return workdir

def getPyPath(script):
    fn = os.path.join (root, script)
    if not isexec (fn): raise IOError ("Cannot find " + script)
    return fn

def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK) 

def cat (in_file, out_file): out_file.write (in_file.read ())

def runPP (workdir, in_name):     
    '''pre-processing '''
    print "[pavy] in_name = ", in_name

    ### return the name of the file after pre-processing
    return in_name
def runProc (args, fname, stdout, stderr, cpu=-1, mem=-1):
    '''Kicks off a specified exec (args) on input fname, with specified 
    stdout/stderr
    ''' 
    args += " " + fname
    if verbose: 
        print "[pavy] kicking off ", args
        
    def _set_limits ():
        if mem > 0:
            mem_b = mem * 1024 * 1024
            resource.setrlimits (resource.RLIMIT_AS, [mem_bytes, mem_bytes])
        if cpu > 0:
            resource.setrlimits (resource.RLIMIT_CPU, [cpu, cpu])

    return sub.Popen (args.split(),
                      stdout=open (stdout, 'w'),
                      stderr=open (stderr, 'w'),
                      preexec_fn=_set_limits)
    
def run (workdir, fname, cpu=-1, mem=-1):
    '''Run everything and wait for an answer'''

    print "[pavy] starting run with fname={f}".format(f=fname)
    
    print "BRUNCH_STAT Result UNKNOWN"
    sys.stdout.flush ()

    print "[pavy] running pp" 
    pp_name = runPP (workdir, fname)
    print "[pavy] finished pp, output={f}".format(f=pp_name)

    ### XXX Find avy and other necessary executables
    
    ## names of configurations
    conf_name = [] 
    ### commands of the configurations
    conf_cmd = list ()
    ## Append configuration options
    # conf_cmd.append ()
    # conf_cmd.append ()


    name = os.path.splitext (os.path.basename (pp_name))[0]
    stdout = [os.path.join (workdir, name + '_avy{}.stdout'.format (i)) 
              for i in range(len (conf_cmd))]
    stderr = [os.path.join (workdir, name + '_avy{}.stderr'.format (i))
              for i in range (len (conf_cmd))]
    
    global running
    running.extend ([runProc (conf_cmd [i], pp_name, stdout[i], stderr [i])
                     for i in range (len (conf_cmd))])

    orig_pids = [p.pid for p in running]
    pids = [p.pid for p in running ]
    pid = -1
    exit_code = 2
    returnvalue = -1
    while len (pids) != 0:
        print "[pavy] running: %r" % pids

        try:
            (pid, returnvalue, ru_child) = os.wait4 (-1, 0)
        except OSError:  # probably got interrupted
            break
        (exit_code, sig) = (returnvalue // 256, returnvalue % 256) 

        print "[pavy] finished pid %d with code %d and signal %d" % (pid, exit_code, sig)

        pids.remove (pid)
        
        # exit codes: 0 = UNSAFE, 1 = SAFE, 2 = UNKNOWN
        if returnvalue == 0:
            for p in pids:
                try:
                    print "[pavy] trying to kill ", p
                    #os.killpg (p, signal.SIGTERM)
                    os.kill(p, signal.SIGTERM)
                except OSError: pass
                finally:
                    try:
                        print "[pavy] waiting for ", p         
                        os.waitpid (p, 0)
                    except OSError: pass
            break
    
    if returnvalue == 0:
        idx = orig_pids.index (pid)
        cat (open (stdout [idx]), sys.stdout)
        cat (open (stderr [idx]), sys.stderr)
        print 'WINNER: ', avy [idx]
        print 'BRUNCH_STAT config {0}'.format (idx)
        print 'BRUNCH_STAT config_name {0}'.format (conf_name [idx])
        print 'BRUNCH_STAT Result ' + ('FALSE' if exit_code == 0 else 'TRUE')
    else:  
        print "ALL INSTANCES FAILED"
        print 'Calling sys.exit with {}'.format (returnvalue // 256)
        print 'BRUNCH_STAT Result UNKNOWN'
        sys.exit (returnvalue // 256)

    running[:] = []
    return exit_code

def main (argv):
    os.setpgrp ()

    (opt, args) = parseOpt (argv[1:])

    workdir = createWorkDir (opt.temp_dir, opt.save_temps)
    returnvalue = 0
    for fname in args:
        returnvalue = run(workdir, fname=fname)
    return returnvalue

def killall ():
    global running
    for p in running:
        try:
            if p.poll () == None:
                p.terminate ()
                p.kill ()
                p.wait ()
                # no need to kill pg since it kills its children
        except OSError:   pass
    running[:] = []

if __name__ == '__main__':
    # unbuffered output
    sys.stdout = os.fdopen (sys.stdout.fileno (), 'w', 0)
    try:
        signal.signal (signal.SIGTERM, lambda x, y: killall())
        sys.exit (main (sys.argv))
    except KeyboardInterrupt: pass
    finally: killall ()
            
