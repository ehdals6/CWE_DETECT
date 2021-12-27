(require memcheck)

(defmethod call (name ptr)
  (when (and ptr (= name 'free)
             (not (= ptr *malloc-zero-sentinel*)))
    (memcheck-release 'alloc ptr)))

(defmethod call (name ptr)
  (when (and ptr (= name '_free)
             (not (= ptr *malloc-zero-sentinel*)))
    (memcheck-release 'alloc ptr)))

(defmethod call (name ptr)
  (when (and ptr (= name '_m_free)
             (not (= ptr *malloc-zero-sentinel*)))
    (memcheck-release 'alloc ptr)))

(defmethod call (name ptr)
  (when (and ptr (= name '_mbuf_freem)
             (not (= ptr *malloc-zero-sentinel*)))
    (memcheck-release 'alloc ptr)))

(defmethod call (name ptr)
  (when (and ptr (= name '_m_freem)
             (not (= ptr *malloc-zero-sentinel*)))
    (memcheck-release 'alloc ptr)))

(defmethod call-return (name len ptr)
  (when (and len ptr (= name 'malloc))
    (memcheck-acquire 'alloc ptr len)))

(defmethod call-return (name len ptr)
  (when (and len ptr (= name '_malloc))
    (memcheck-acquire 'alloc ptr len)))

(defmethod call-return (name sopt mp)
  (when (and mp sopt (= name '_soopt_getm))
    (memcheck-acquire 'alloc mp 8)))

(defmethod call-return (name ptr1 ptr2 ptr)
  (when (and ptr1 ptr2 (= name '_soopt_getm))
    (memcheck-acquire 'alloc ptr2 8)))
