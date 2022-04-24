(define make-ok
(lambda (val)
  (cons 'ok val)
)
)

(define make-error
(lambda (msg)
  (cons 'error msg)
)
)

(define ok?
(lambda (res)
  (eq? (car res) 'ok)
)
)

(define error? 
(lambda (res)
  (eq? (car res) 'error)
)
)

(define result?
(lambda (res)
  (or (ok? res) (error? res))
)
)

(define result->val
(lambda (res)
  (cdr res)
)
)

; Signature: bind(f)
; Type: (f:(T->RES)) -> (RES)->RES
; Purpose:
; Pre-conditions:
; Tests:
(define bind 
(lambda (f)
  (lambda (result)
   (if(ok? result)
    (f(cdr result))
    (result))
  )
)
)

(define make-dict
(lambda ()
(cons 'dict '() )
)
)

(define dict?
(lambda (e)
  (eq? (car e) 'dict)
)
)

(define getRec
(lambda (dict k)
  (if (eq? dict '())
    (make-error "Key not found")
    (if (eq? (caar dict) k)
      (make-ok(cdar dict))
      (getRec (cdr dict) k)
    )
  )
)
)
(define get
(lambda (dict k)
  (if (dict? dict) 
      (getRec (cdr dict) k)
      (make-error "Error: not a dictionary")
  )
)
)

(define put
(lambda (dict k v)
(if (dict? dict)
    (if (ok? (get dict k)) ;this used get in order to check if k is in dict
        (make-ok(cons (car dict) (putRec (cdr dict) k v))) 
        (make-ok(cons (car dict) (cons (cons k v) (cdr dict)))))
    (make-error "Error: not a dictionary")
  )
)
)

(define putRec
(lambda (dict k v)
(if (eq? (caar dict) k)
(cons (cons k v) (cdr dict))
(cons (car dict) (putRec (cdr dict) k v))     
)
)
)
(define make-empty-list
(lambda ()
  '()
)
)


(define map-dict-rec
(lambda (dict f)
  (if (eq? dict '())
    (make-empty-list)
    (cons (cons (caar dict) (f (cdar dict))) (map-dict-rec (cdr dict) f)))
)
)


(define map-dict
(lambda (dict f)
  (if (dict? dict)
    (make-ok (cons 'dict (map-dict-rec (cdr dict) f)))
    (make-error "Error: not a dictionary")
  )
)
)

(define filter-dict-rec
(lambda (dict pred)
  (if (eq? dict '())
    (make-empty-list)
    (if (eq? (pred (caar dict) (cdar dict)) #t)
        (cons (car dict) (filter-dict-rec (cdr dict) pred))
        (filter-dict-rec (cdr dict) pred))
    )
)
)


(define filter-dict
(lambda (dict pred)
  (if (dict? dict)
    (make-ok (cons 'dict (filter-dict-rec (cdr dict) pred)))
    (make-error "Error: not a dictionary")
  )
)
)
