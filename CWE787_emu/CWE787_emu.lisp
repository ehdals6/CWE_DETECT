(require incident)

(defparameter *readflag* 0)

(defun set/region (len ptr)
  (region-create 'malloc ptr (-1 (ptr+ char ptr len)))
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

(defmethod stored (ptr val)
  (when (and (= *readflag* 1) (< ptr *malloc-arena-end*) (> ptr *malloc-arena-start*))
    (when (not (region-contains 'malloc ptr))
      (incident-report 'CWE_787)
    );;=>(set *readflag* 0)
  )
)


