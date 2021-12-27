(require incident)

(defmethod call (_)
 (incident-report 'TEST)

)
