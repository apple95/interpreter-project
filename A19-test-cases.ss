; After loading your interpreter and doing (rep), 
; paste these expressions one-at-a-time into Scheme window.
; There will not be test cases on the server.




(eval-one-exp '
(+ 5 (call/cc 
  (lambda (k) (+ 6 (k 7)))))) ; 1. answer: 12      15 points


(eval-one-exp '
(+ 3 (call/cc (lambda (k) (* 2 5)))))  ; 2. answer: 13  5 points


(begin
  (reset-global-env)
  (eval-one-exp '
   (define xxx #f))
  (eval-one-exp '
   (+ 5 (call/cc (lambda (k) 
		   (set! xxx k)
		   2))))
  (eval-one-exp '
   (* 7 (xxx 4)))) ; answer: 9                       15 points

(eval-one-exp '(call/cc procedure?)) ; answer:  #t   10 points

(begin 
  (reset-global-env)
  (eval-one-exp '
   (define strange1
     (lambda (x)
       (display 1)
       (call/cc x)
       (display 2)
       (newline))))
  
  (eval-one-exp '
   (strange1 (call/cc (lambda (k) (k k))))))  ; answer: 112     25  points




;----------------   exit

(begin
  (reset-global-env)
  (eval-one-exp '
   (+ 4 (exit 5 (exit 6 7))) ; answer (6 7)        5 points
))

(begin
  (reset-global-env)
  (eval-one-exp '
   (+  3 (- 2 (exit 5)))))   ; answer (5)         5 points

(begin
  (reset-global-env)
  (eval-one-exp '
   (- 7 (if (exit 3) 4 5)))) ; answer (3)         5 points

(begin 
  (reset-global-env)		    
  (eval-one-exp '(call/cc (lambda (k) (+ 100 (exit (+ 3 (k 12))))))))  ; Answer 12      8 points

(begin
  (reset-global-env)
  (eval-one-exp '(call/cc (lambda (k) (+ 100 (k (+ 3 (exit 12)))))))) ; answer (12)     7 points


		
