;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 



;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

;; Parsed expression datatypes
(define-datatype expression expression?  ; based on the simple expression grammar, EoPL-2 p6
  (var-exp 
    (id symbol?))
  (lambda-symbol-exp
    (id symbol?)
    (body (list-of expression?)))
  (lambda-pair-exp
   (id pair?)
   (body (list-of expression?)))
  (lambda-exp
     (id (list-of symbol?))
    (body (list-of expression?)))
  (let-exp
   (ids (list-of symbol?))
   (exprs (list-of expression?))
   (body (list-of expression?)))
  (named-let-exp
   (id symbol?)
   (vars (list-of symbol?))
   (exprs (list-of expression?))
   (body (list-of expression?)))
  (let*-exp
   (ids (list-of symbol?))
   (exprs (list-of expression?))
   (body (list-of expression?)))
  (letrec-exp
   (methods (list-of expression?))
   (body (list-of expression?)))
  (if-exp
   (test expression?)
   (then-body expression?))
  (if-else-exp
   (test expression?)
   (then-body expression?)
   (else-body expression?))
  (while-exp
    (test expression?)
    (body (list-of expression?)))
  (set!-exp
   (id symbol?)
   (body expression?))
  (lit-exp 
   (data lit-exp?))
  (begin-exp
   (bodies (list-of expression?))) 
  (cond-exp
   (clauses (list-of clause?)))
  (case-exp
   (key expression?)
   (clauses list?))
  (else-exp
   (bodies (list-of expression?)))
  (or-exp
   (bodies (list-of expression?)))
  (app-exp
    (rator expression?)
    (rand (list-of expression?))))

(define clause?
  (lambda (x)
    (or (expression? x) (and (expression? (car x)) ((list-of expression?) (cdr x))))))
	
; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.


	 

	
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))


(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (params (list-of symbol?))
   (body (list-of expression?))
   (env environment?)]
  [closure-for-lambda-symbol
    (params (list-of symbol?))
    (body (list-of expression?))
    (env environment?)]
)

(define (cell val)
  (cons val 'its-a-cell))
(define cell-ref car)
(define set-cell! set-car!)
(define (cell? x)
  (and (pair? x) (eqv? (cdr x) 'its-a-cell)))



;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)


;;checks if a list is a variable list in let
(define let-list?
  (lambda (ls)
    (andmap (lambda (x) (and (symbol? (car x)) (expression? (cadr x)))) ls)))
;;checks if an element is a 'lit'
(define lit-exp?
  (lambda (datum)
    (or (symbol? datum) (number? datum) (string? datum) (boolean? datum) (vector? datum) (list? datum))))
		  
		      
;;
(define parse-exp
  (lambda (datum)
    (cond
      ((symbol? datum) (var-exp datum))
      ((or (number? datum) (string? datum) (boolean? datum) (vector? datum)) (lit-exp datum))
      ((list? datum)
       (cond
       ((equal? (car datum) 'quote) (lit-exp (cadr datum)))
       ((eqv? (car datum) 'lambda)
	(if (<= (length (cdr datum)) 1) (eopl:error 'parse-exp "Invalid lambda expression length ~s" datum)
	    (if (symbol? (cadr datum)) (lambda-symbol-exp (cadr datum) (map parse-exp (cddr datum)))
		(if (or (null? (cadr datum)) (pair? (cadr datum)))
		    (if (list? (cadr datum))
			       (if (or (null? (cadr datum)) (andmap symbol? (cadr datum)))
				   (lambda-exp (cadr datum) (map parse-exp (cddr datum))) 
				   (eopl:error 'parse-exp "Invaild arguments in lambda expression. Must be symbols: ~s" datum))
			       (if (not (and-pred-imlist (cadr datum) symbol?)) (eopl:error 'parse-exp "Invalid arguments in lambda expression. Must be symbols: ~s" datum)
				   (lambda-pair-exp (cadr datum) (map parse-exp (cddr datum)))))
		    (eopl:error 'parse-exp "Invaild arguments in lambda expression. Must be symbols: ~s" datum)))))
       ((eqv? (car datum) 'let)
	(if (symbol? (cadr datum))
	    (if (> (length (cdr datum)) 2)
		(if (test-let-vars? (caddr datum))
		    (named-let-exp (cadr datum) (map (lambda (x) (car x)) (caddr datum)) (map (lambda (x) (parse-exp (cadr x))) (caddr datum))
		     (map parse-exp (cddr datum)))
		    (eopl:error 'parse-exp "Invaild variables in named let expression. ~s" datum))
		(eopl:error 'parse-exp "Invalid length of named-let expression. ~s" datum))
	    (if (> (length (cdr datum)) 1)
		(if (test-let-vars? (cadr datum))
		    (let-exp (map (lambda (x) (car x)) (cadr datum)) (map (lambda (x) (parse-exp (cadr x))) (cadr datum))
		     (map parse-exp (cddr datum)))
		    (eopl:error 'parse-exp "Invaild variables in let expression. ~s" datum))
		(eopl:error 'parse-exp "Invalid length of let expression. ~s" datum))
	))
	((eqv? (car datum) 'let*)
	 (if (> (length (cdr datum)) 1)
		(if (test-let-vars? (cadr datum))
		    (let*-exp (map (lambda (x) (car x)) (cadr datum)) (map (lambda (x) (parse-exp (cadr x))) (cadr datum))
		     (map parse-exp (cddr datum)))
		    (eopl:error 'parse-exp "Invaild variables in let* expression. ~s" datum))
		(eopl:error 'parse-exp "Invalid length of let* expression. ~s" datum))
	 )
	 ((eqv? (car datum) 'letrec)
	  (if (> (length (cdr datum)) 1)
		(if (test-let-vars? (cadr datum))
		    (letrec-exp (map parse-exp (cadr datum)) (map parse-exp (cddr datum)))
		    (eopl:error 'parse-exp "Invaild variables in let* expression. ~s" datum))
		(eopl:error 'parse-exp "Invalid length of let* expression. ~s" datum))
	  )
	 ((eqv? (car datum) 'if)
	  (if (not (or (eq? 2 (length (cdr datum))) (eq? 3 (length (cdr datum))))) (eopl:error 'parse-exp "Invaild if statement, incorrect number of bodies ~s" datum)
	      (if (null? (cdddr datum))
			 (if-exp (parse-exp (cadr datum)) (parse-exp (caddr datum)))
			 (if-else-exp (parse-exp (cadr datum)) (parse-exp (caddr datum)) (parse-exp (cadddr datum))))))
	 ((eqv? (car datum) 'while) 
	  (while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))
	  )
	 ((eqv? (car datum) 'begin)
	  (begin-exp (map parse-exp (cdr datum))))
	 ((eqv? (car datum) 'or)
	  (or-exp (map parse-exp (cdr datum))))
	 ((eqv? (car datum) 'cond)
	  	(cond-exp (cond-helper (cdr datum))))
	 ((eqv? (car datum) 'case)
	  (case-exp (parse-exp (cadr datum)) (map (lambda (x) (if (eqv? (car x) 'else) (else-exp (map parse-exp (cdr x)))(list (car x) (map parse-exp (cdr x))))) (cddr datum))))
	 ((eqv? (car datum) 'set!)
	  (cond
	   ((not (eq? 2 (length (cdr datum)))) (eopl:error 'parse-exp "Invalid set! expression length ~s" datum))
	   ((not (symbol? (cadr datum))) (eopl:error 'parse-exp "Invalid first arguemtn for set! expression ~s" datum))
	  (else (set!-exp (cadr datum) (parse-exp (caddr datum))))))
         (else
	   (app-exp
           (parse-exp (car datum))
           (map parse-exp (cdr datum))))))
      (else (eopl:error 'parse-exp
              "Invalid concrete syntax ~s" datum)))))
(define and-pred-imlist
  (lambda (ls pred)
    (if (pair? (cdr ls)) (and (pred (car ls)) (and-pred-imlist (cdr ls) pred))
	(and (pred (car ls)) (pred (cdr ls))))))
(define test-let-vars?
  (lambda (ls)
    (and (list? ls) (andmap (lambda (a) (and (list? a) (eq? 2 (length a)) (symbol? (car a)))) ls))))
(define cond-helper
  (lambda (datum)
    (if (not (null? datum))
	(if (not (andmap list? datum)) (eopl:error 'parse-exp "Invalid cond expression, clause not a list ~s" datum)
	    (let ((x (car datum)))
	      (if (eq? (car x) 'else)
		  (if (not (null? (cdr datum))) (eopl:error 'parse-exp "Invalid else statement in cond expression ~s" datum) 
		      (list (else-exp (map parse-exp (cdr x)))))
		  (append (list (map parse-exp x))
		    (cond-helper (cdr datum)))))))))
;;
(define unparse-exp ; an inverse for parse-exp
  (lambda (exp)
    (cases expression exp
      (var-exp (id) id)
      (lit-exp (data) data)
      (lambda-exp (id body)
        (append (list 'lambda id)
          (map unparse-exp body)))
      (lambda-symbol-exp (id body)
	(append (list 'lambda id) (map unparse-exp body)))
      (let-exp (ids exprs body)
	       (append (list 'let (let-unparse-helper ids exprs)) (map unparse-exp body)))
      (named-let-exp (id vars exprs body)
		    (append (list 'let id (let-unparse-helper ids exprs))  (map unparse-exp body)))
      (let*-exp (ids exprs body)
		(append (list 'let* (let-unparse-helper ids exprs)) (map unparse-exp body)))
      (letrec-exp (methods body)
		 (append (list 'letrec (map unparse-exp methods)) (map unparse-exp body)))
      (if-exp (test then-body) 
	      (list 'if (unparse-exp test) (unparse-exp then-body)))
      (if-else-exp (test then-body else-body)
	       (list 'if (unparse-exp test) (unparse-exp then-body) (unparse-exp else-body)))
      (while-exp (test body) (cons (unparse-exp test) (map unparse-exp body)))
      (set!-exp(id body)
	   (list 'set! id (unparse-exp body)))
  (app-exp (rator rand)
        (cons (unparse-exp rator)
              (map unparse-exp rand))))))
(define let-unparse-helper
  (lambda (ls1 ls2)
    (if (null? ls1) '()
	(cons (list (car ls1) (unparse-exp (car ls2))) (let-unparse-helper (cdr ls1) (cdr ls2))))))







;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))
;;apply-env-ref
(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      (empty-env-record ()
        (fail))
      (extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	      (succeed (list-ref vals pos))
	      (apply-env env sym succeed fail)))))))



;;(define apply-env
  ;;(lambda (env var)
    ;;(deref (apply-env-ref env var))))

;;(define deref cell-ref)
;;(define set-ref! set-cell!)


;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+
(define syntax-expand
  (lambda (exp)
    (cases expression exp
	   (var-exp (id) exp)
	   (lit-exp (data) exp)
	   (lambda-exp (id body) (lambda-exp id (map syntax-expand body)))
	   (lambda-symbol-exp (id body) (lambda-symbol-exp id (map syntax-expand body)))
	   (named-let-exp (id vars exprs body) exp)
	   (let-exp (ids exprs body) (app-exp (syntax-expand (lambda-exp ids body)) (map syntax-expand exprs)))
	   (let*-exp (ids exprs body) (syntax-expand (let-exp ids exprs body)))
	   (letrec-exp (methods body) exp)
	   (if-exp (bool body) (if-exp (syntax-expand bool) (syntax-expand body)))
	   (if-else-exp (bool body1 body2) (if-else-exp (syntax-expand bool) (syntax-expand body1) (syntax-expand body2)))
	   (begin-exp (bodies) (app-exp (lambda-exp '() (map syntax-expand bodies)) '()))
	   (cond-exp (clauses) (syntax-cond-helper clauses))
	   (case-exp (key clauses) (syntax-case-helper key clauses))
	   (while-exp (test body) exp)
	   (else-exp (bodies) (app-exp (lambda-exp '() (map syntax-expand bodies)) '()))
	   (set!-exp (id body) exp)
	   (or-exp (bodies) (syntax-or-helper bodies))
	   (app-exp (rator rand) (app-exp (syntax-expand rator) (map syntax-expand rand))))))



; To be added later
(define syntax-cond-helper
  (lambda (ls)
    (if (null? ls) (void)
	(if (expression? (car ls)) (syntax-expand (car ls))
	    (if-else-exp (syntax-expand (1st (car ls))) (syntax-expand (2nd (car ls))) (syntax-cond-helper (cdr ls)))))))
(define syntax-case-helper
  (lambda (key ls)
    (if (null? ls) (void)
	(let ((x (car ls)))
	  (if (expression? x) (syntax-expand (car ls))
	      (let ((y (list (lit-exp (1st x)) key)))
	    (if-else-exp (app-exp (var-exp 'contains?) y) (syntax-expand (begin-exp (2nd x))) (syntax-case-helper key (cdr ls)))))))))
(define syntax-or-helper
  (lambda (ls)
    (if (null? ls) (lit-exp #f)
	(let ((x (syntax-expand (car ls))))
	(if (null? (cdr ls)) x
        (if-else-exp x x (syntax-or-helper (cdr ls))))))))




;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+
(define *prim-proc-names* '(+ - * /  add1 sub1 zero? not cons = and < > <= >= car cdr list null? assq eq? eqv? equal? atom? length list->vector list? pair? procedure? vector vector->list make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! display newline caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cddr contains? quotient apply map))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))
	 


; top-level-eval evaluates a form in the global environment
(define global-env init-env)

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form global-env)))


; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
				(apply-env env id; look up its value.
      	   (lambda (x) x) ; procedure to call if id is in the environment 
           (lambda () (apply-env global-env id
				 (lambda (x) x) 
				 (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
							"variable not found in environment: ~s"
							id)))))]
      [let-exp (ids exprs bodies)
	       (let ((envir (extend-env ids (map (lambda (x) (eval-exp x env)) exprs) env)))
		 (eval-exp-loop bodies envir))]
      ;;(let loop ([bodies bodies])
		   ;;(if (null? (cdr bodies))
		     ;;  (eval-exp (car bodies) envir)
		       ;;(begin
			 ;;(eval-exp (car bodies) envir)
			 ;;(loop (cdr bodies))))))]
    
      [if-else-exp (test then-body else-body)
	      (if (eval-exp test env) (eval-exp then-body env) (eval-exp else-body env))]
      [if-exp (test then-body)
        (if (eval-exp test env) (eval-exp then-body env))
      ]
      [lambda-exp (args body)
		  (closure args body env)]
      [lambda-symbol-exp (arg body)
      (closure-for-lambda-symbol (list arg) body env)
      ]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
      [while-exp (test body) (eval-exp-while-loop test body env)]  
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

;;performs eval exp on all bodies in the current environment
(define eval-exp-loop
  (lambda (bodies env)
    (if (null? (cdr bodies)) (eval-exp (car bodies) env)
	(begin
	  (eval-exp (car bodies) env)
	  (eval-exp-loop (cdr bodies) env)))))

(define eval-exp-while-loop
  (lambda (test bodies env)
    (letrec ([helper (lambda (test all-body rest-of-body env) 
      (if (null? (cdr rest-of-body)) 
      (begin (eval-exp (car rest-of-body) env) 
             (if (not (equal? #f (eval-exp test env)))
              (helper test all-body all-body env)
             )) 
    (begin
    (eval-exp (car rest-of-body) env)
    (helper test all-body (cdr rest-of-body) env))))])
    (if (not (equal? #f (eval-exp test env)))
              (helper test bodies bodies env)
             )
    )))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure (params body env)
	       (let ([extended-env (extend-env params args env)])
		    (eval-exp-loop body extended-env))]
      [closure-for-lambda-symbol (params body env)
         (let ([extended-env (extend-env params (list args) env)])
        (eval-exp-loop body extended-env))]
			; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))



; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.
  
(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)] ;;needs multiple args
      [(-) (apply - args)]
      [(*) (apply * args)] ;;needs multiple args
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(and) (andmap args)]
      [(<) (< (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) (my-list args)] ;;needs multiple args
      [(null?) (null? (1st args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(atom?) (atom? (1st args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (or (procedure? (1st args)) (proc-val? (1st args)))]
      [(vector->list) (vector->list (1st args))]
      [(vector) (apply vector args)] ;;needs multiple args
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display (1st args))]
      [(newline) (newline)]
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cdar) (cdar (1st args))]
      [(cddr) (cddr (1st args))]
      [(caaar) (caaar (1st args))]
      [(caadr) (caadr (1st args))]
      [(cadar) (cadar (1st args))]
      [(caddr) (caddr (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(cddar) (cddar (1st args))]
      [(cdddr) (cdddr (1st args))]
      [(contains?) [my-contains (1st args) (2nd args)]]
      [(quotient) (apply quotient args)]
      [(map)   (apply my-map (1st args) (cdr args))]
      [(apply) (apply (1st args) (cddr args))] ;;need to implement this
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-op)])))
(define my-map
  (lambda (f ls . more)
    (if (null? more)
        (let map1 ((ls ls))
          (if (null? ls)
              '()
              (cons (f (car ls))
                    (map1 (cdr ls)))))
        (let map-more ((ls ls) (more more))
          (if (null? ls)
              '()
              (cons (apply f (car ls) (my-map car more))
                    (map-more (cdr ls)
                              (my-map cdr more))))))))
(define my-contains
  (lambda (ls obj)
    (if (null? ls) #f
	(if (eqv? (car ls) obj) #t
	    (my-contains (cdr ls) obj)))))
(define my-list
  (lambda (args)
    (if (null? args) '()
	(cons (car args) (my-list (cdr args))))))
(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([input (read)])
        (if (equal? input '(exit))
        (display "")   ;Exits the rep loop without printing anything
        (let ([answer (top-level-eval (syntax-expand (parse-exp input)))])
      ;; TODO: are there answers that should display differently?
        (eopl:pretty-print answer) (newline)
        (rep)
        )
        )
      
    )
  )
)  ; tail-recursive, so stack doesn't grow.



(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))