;; generated primitives
(define-primitive '%halt 0 0)
(define-primitive 'pair? 1 1)
(define-primitive 'cons 2 2)
(define-primitive 'car 1 3)
(define-primitive 'cdr 1 4)
(define-primitive 'set-car! 2 5 #:unspecified-result)
(define-primitive 'set-cdr! 2 6 #:unspecified-result)
(define-primitive 'null? 1 7)
(define-primitive 'number? 1 8)
(define-primitive '= 2 9)
(define-primitive '%+ 2 10)
(define-primitive '%- 2 11)
(define-primitive '%mul-non-neg 2 12)
(define-primitive '%div-non-neg 2 13)
(define-primitive '%rem-non-neg 2 14)
(define-primitive '< 2 15)
(define-primitive '> 2 16)
(define-primitive 'logior 2 17)
(define-primitive 'logxor 2 18)
(define-primitive 'eq? 2 19)
(define-primitive 'not 1 20)
(define-primitive 'symbol? 1 21)
(define-primitive 'boolean? 1 22)
(define-primitive 'string? 1 23)
(define-primitive 'string->list 1 24)
(define-primitive 'list->string 1 25)
(define-primitive 'u8vector? 1 26)
(define-primitive '%make-u8vector 1 27)
(define-primitive 'u8vector-ref 2 28)
(define-primitive 'u8vector-set! 3 29 #:unspecified-result)
(define-primitive 'u8vector-length 1 30)
(define-primitive 'return 1 31)
(define-primitive 'pop 0 32 #:unspecified-result)
(define-primitive 'get-cont 0 33)
(define-primitive 'graft-to-cont 2 34 #:unspecified-result)
(define-primitive 'return-to-cont 2 35)
(define-primitive 'graft-to-cont 2 34 #:unspecified-result)
(define-primitive 'return-to-cont 2 35 )
(define-primitive 'print 1 36 #:unspecified-result)
(define-primitive 'clock 0 37 )
(define-primitive 'motor 2 38 #:unspecified-result)
(define-primitive 'led 3 39 #:unspecified-result)
(define-primitive '%led2-color 1 40 #:unspecified-result)
(define-primitive '%getchar-wait 2 41 )
(define-primitive '%putchar 2 42 )
(define-primitive 'beep 2 43 )
(define-primitive 'adc 1 44 )
(define-primitive 'sernum 0 45 )
(define-primitive 'network-init 0 46 #:unspecified-result)
(define-primitive 'network-cleanup 0 47 #:unspecified-result)
(define-primitive 'receive-packet-to-u8vector 1 48 )
(define-primitive 'send-packet-from-u8vector 2 49 )
