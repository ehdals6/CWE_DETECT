(require incident)

(defparameter *readflag* 0)

(defun set/region (len ptr)
  (region-create 'malloc ptr (-1 (ptr+ char ptr len)))
  (incident-report 'TAINT)
)

(defmethod call-return (name len ptr)
  (when (= name '_malloc)
  (set/region len ptr)
  )
)

(defmethod read (reg ptr)
  (when (and (= reg 'RAX) (= ptr (region-lower 'malloc ptr)))
    (set *readflag* 1)
  )
)

(defmethod loaded (ptr val)
  (when (and (= *readflag* 1) (< ptr *malloc-arena-end*) (> ptr *malloc-arena-start*))
    (when (not (region-contains 'malloc ptr))
      (incident-report 'CWE_125)
    );;=>(set *readflag* 0)
  )
)

