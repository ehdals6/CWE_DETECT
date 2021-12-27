(parameter depth 32768 "a depth of analysis")
(parameter entry-points all-subroutines "where to search")

(option primus-lisp-load
  posix
  CWE787_emu)

(option primus-lisp-add $prefix)

(option passes
        run)

(option primus-lisp-channel-redirect
  <stdin>:$prefix/stdin
  <stdout>:$prefix/stdout
  <stderr>:$prefix/stderr)

(option primus-print-output incidents)
(option primus-promiscuous-mode)
(option primus-greedy-scheduler)
(option primus-limit-max-length $depth)
(option run-entry-points ${entry-points})

(option primus-print-obs
 incident
 call
 call-return
)


