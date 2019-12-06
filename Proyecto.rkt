#lang nanopass
(require nanopass/base)
(require 2htdp/batch-io)

;; Definición del predicado que verifica las variables
(define (variable? x)
  (symbol? x))

;; Definición del predicado que verifica las constantes
(define(constant? c)
  (or(boolean? c)
     (integer? c)
     (char? c)))

;; Definición del predicado que verifica las primitivas del lenguaje
(define primitive?
        (lambda (pr)
          (memq pr '(+ - * / < > equal? iszero? ++ -- and or not length car cdr))))

;; Definición del predicado que verifica los tipos
;; Int | Char | Bool | Lambda | List | (List of T) | (T → T)
(define (type? x) (or (b-type? x) (c-type? x)))
;;Verifica si es un tipo basico
(define (b-type? x) (memq x '(Bool Char Int List String Lambda)))
;; Verifica si es un tipo compuesto
(define (c-type? x) (if (list? x) 
	(let* (
		[f (car x)]
		[s (cadr x)]
		[t (caddr x)])
	(or (and (equal? f 'List) (equal? s 'of) (type? t)) 
		(and (type? f) (equal? s '→) (type? t))))
	#f))

;;nuevo predicado para el nuevo lenguaje L4
(define (primitiva? x) (memq x '(+ - * / length car cdr)))

(define (ArrayLength? x)
  (integer? x))

(define (log-primitive? x) (memq x '(+ - * / ++ -- < > equal? length car cdr void)))

(define (c-quote? x)
  (or (integer? x)
      (boolean? x)))

;; Definición del Lenguaje Fuente
(define-language LF
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (string (s))
   (type (t)))
  (Expr (e body)
    x
    c
    l
    s
    pr
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* e)
    (e0 e1 ...)))

(define-language L1
  (extends LF)
  (Expr (e body)
        (- (if e0 e1))))

(define-language L2
  (extends L1)
  (terminals
   (-(string (s))))
  (Expr (e body)
        (- s)))

(define-language L3
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (type (t)))
  (Expr (e body)
    x
    c
    l
    pr
    (begin e* ... e)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)
    (let ([x* t* e*] ...) body)
    (letrec ([x* t* e*] ...) body)
    (list e* e)
    (e0 e1 ...)))

(define-language L4
  (extends L3)
  (terminals
   (-(primitive(pr)))
   (+ (log-primitive(pr)))))

(define-language L5
  (extends L4)
  (Expr (e body)
        (- pr)
        (+ (primapp pr e* ...))))

(define-language L6
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    (quot c)
    (begin e* ... e)
    (primapp pr e* ...)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)
    (let ([x* t* e*] ...) body)
    (letrec ([x* t* e*] ...) body)
    (list e* ...)
    (e0 e1 ...)))

;Lenguaje L7,extiende a L6
(define-language L7
  (extends L6)
  (Expr (e body)
        (- (let ([x* t* e*]...) body)
           (letrec ([x* t* e*]...) body)
           (lambda ([x* t*] ...) body))
        (+ (let ([x t e]) body)
           (letrec ([x t e]) body)
           (lambda ([x t] ...) body))))

;Lenguaje L8, extiende a L7
(define-language L8
  (extends L7)
  (Expr (e body)
        (+ (letfun ([x t e]) body))))

(define-language L9
  (extends L8)
  (Expr (e body)
         (- (lambda ([x t] ...) body)
            (e0 e1 ...))
         (+ (lambda ([x t]) body)
            (e0 e1))))

(define-language L10
  (extends L9)
  (Expr (e body)
        (- (quot c))
        (+ (const t c))))

(define-language L11
  (extends L10)
  (Expr (e body)
        (- (lambda ([x t]) body))
        (+ (lambda ([x t]...) body))))

(define-language L12
  (extends L11)
  (Expr (e body)
        (- (let ([x t e]) body)
           (letrec ([x t e]) body)
           (letfun ([x t e]) body))
        (+ (let body)
           (letrec body)
           (letfun body))))

;; Función parser del lenguaje LF
(define-parser parser-LF LF)
(define-parser parser-L1 L1)
(define-parser parser-L2 L2)
(define-parser parser-L3 L3)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)
(define-parser parser-L11 L11)
(define-parser parser-L12 L12)


;; Procesos

;;-------------------------------------------------------- Practica 2
;; Proceso del compilador encargado de eliminar la expresion if sin el caso para else.
(define-pass remove-one-armed-if : LF(ir) -> L1 ()
  (Expr : Expr (ir) -> Expr ()
        [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]
        [(if ,[e0] ,[e1] ,[e2]) `(if ,e0 ,e1 ,e2)]))

;; Procesp del compilador encargado de eliminar las cadenas como elementos
;; terminales del lenguaje.
(define-pass remove-string : L1(ir) -> L2 ()
  (Expr : Expr (ir) -> Expr ()
        [(unquote s) (string->list s)]))

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : L2 (ir) -> L3 ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))
;;--------------------------------------------------------Practica 3


(define-pass remove-logical-operators : L3 (ir) -> L4 ()
  (definitions
    (define (and? x)
      (memq x '(and)))
    (define (or? x)
      (memq x '(or)))
    (define (not? x)
      (memq x '(not))))
  (Expr : Expr (ir) -> Expr ()
    [(,pr , [e0*]) (cond
                     [(not? pr)`(if ,e0* #f #t)]
                     [else `(,pr ,e0*)])]
    [(,pr , [e0*] ,[e1*]) (cond
                          [(and? pr) `(if ,e0* ,e1* #f)]
                          [(or? pr) `(if ,e0* #t ,e1*)]
                          [else `(,pr ,e0* ,e1*)])]))

;; Proceso para el Ejercicio 4 del Proyecto (Agregar mas primitivas al lenguaje)
(define-pass remove-arit-operators : L4 (ir) -> L4()
  (Expr : Expr (ir) -> Expr ()
        [(,pr , [e0*]) (cond
                        [(equal? '++ pr) `(+ ,e0* 1)]
                        [(equal? '-- pr) `(- ,e0* 1)]
                        [(equal? 'iszero? pr) `(equal? ,e0* 0)]
                        [else error "Error 1 :v"])]
        [(,pr , [e0*] ,[e1*]) (cond
                                [(equal? '++ pr) `,(+ e0* 1)]
                                [else error "Error 2 :v"])]))
; Tabla con sus valores para el ejercicio 2
(define ht (make-hash))
(hash-set! ht '+ 'Integer)
(hash-set! ht '- 'Integer)
(hash-set! ht '* 'Integer)
(hash-set! ht '/ 'Integer)
(hash-set! ht 'car 'List)
(hash-set! ht 'cdr 'List)

; Ejercicio 2
(define-pass eta-expand : L4(ir) -> L5()
  (definitions
    (define (whattype x)
      (let ([type (hash-ref ht x)])
        (cond
          [(equal? type 'Integer) `(lambda ([x0 Int][x1 Int])(primapp ,x x0 x1))]
          [(equal? type 'List) `(lambda ([x0 List]) (primapp ,x x0))]))))
  (Expr : Expr (ir) -> Expr ()
        [(,pr) (whattype pr)]
        [(,pr ,[e0]) `((lambda ([x0 List]) (primapp ,pr x0)) ,e0)]
        [(,pr ,[e0] ,[e1]) `((lambda ([x0 Int][x1 Int]) (primapp ,pr x0 x1)) ,e0 ,e1)]))

; Ejercicio 3
(define-pass quote-const : L5(ir) -> L6()
  (Expr : Expr(ir) -> Expr()
        [,c `(quot ,c)]))

;; (back-end '(if (not (or #t #f)) "hola" (++ 5)))
;;------------------------------------------------------------Practica 4

;Proceso curry-let
(define-pass curry-let : L6 (ir) -> L7 ()
  (definitions
    (define un-6
      (lambda(z)
        (nanopass-case(L6 Expr) z
                      [,x (unparse-L6 z)]
                      [(quot ,c) (unparse-L6 z)]
                      [(primapp ,pr ,e* ...)  (unparse-L6 z)]
                      [(begin ,e* ... ,e) (unparse-L6 z)]
                      [(if ,e0 ,e1 ,e2) (unparse-L6 z)]
                      [(lambda ([,x* ,t*] ...) ,body) (unparse-L6 z)])))
    
    (define (recCurry-let x* t* e* body)
      (cond
        [(null? x*) (unparse-L6 body)]
        [else `(let ([,(car x*) ,(car t*) ,(un-6 (car e*))]) ,(recCurry-let (cdr x*) (cdr t*) (cdr e*) body))]))
    
    (define (recCurry-letrec x* t* e* body)
      (cond
        [(null? x*) (unparse-L6 body)]
        [else `(letrec ([,(car x*) ,(car t*) ,(un-6 (car e*))]) ,(recCurry-letrec (cdr x*) (cdr t*) (cdr e*) body))])))
  
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x* ,t* ,e*]...) ,body) (cond
                                       [(equal? 1 (length x*))
                                        `(let ([,(car x*) ,(car t*) ,(parser-L7(un-6 (car e*)))]) ,(parser-L7(un-6 body)))]
                                       [else `(let ([,(car x*) ,(car t*) ,(parser-L7(un-6 (car e*)))])
                                                ,(parser-L7 (recCurry-let (cdr x*) (cdr t*) (cdr e*) body)))])]
        [(letrec ([,x* ,t* ,e*] ...) ,body) (cond
                                              [(equal? 1 (length x*))
                                               `(letrec ([,(car x*) ,(car t*) ,(parser-L7(un-6(car e*)))]) ,(parser-L7(un-6 body)))]
                                              [else
                                               `(letrec ([,(car x*) ,(car t*) ,(parser-L7(un-6(car e*)))])
                                                  ,(parser-L7(recCurry-letrec (cdr x*) (cdr t*) (cdr e*) body)))])]))

;Proceso identify-assigments
(define-pass identify-assigments : L7 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,[e]]) ,[body]) (if (equal? t 'Lambda)
                                         `(letrec ([,x ,t ,e]) ,body)
                                         ir)]))


;Proceso un-anonymous
(define count 0)
(define-pass un-anonymous : L7 (ir) -> L8 ()
  (definitions
    (define (atarashi-namae)
      (begin
        (define str (string-append "foo" (number->string count)))
        (set! count (+ count 1))
        (string->symbol str))))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t]) ,body)
         (let ([namae (atarashi-namae)])
           `(letfun ([,namae Lambda ,ir]) namae))]))

;Proceso verify-arity
(define-pass verify-arity : L8 (ir) -> L8 ()
  (definitions
    (define (arit? x) (memq x '(+ - * /)))
    (define (lst? x) (memq x '(length car cdr))))
  (Expr : Expr (ir) -> Expr ()
        [(primapp ,pr ,[e*] ...)
         (cond
           [(and (arit? pr) (equal? (length e*) 2)) ir]
           [(and (lst? pr) (equal? (length e*) 1)) ir]
           [else (error "Arity mismatch")])]))

;Fucion auxiliar para verify-vars
(define (union a b)
  (cond
    [(empty? b) a]
    [(member (car b) a) (union a (cdr b))]
    [else (union (cons (car b) a) (cdr b))]))

;Funcion auxiliar para verify-vars
(define (rmvl lst x)
  (cond
    [(member x lst) (rmvl (remove x lst) x)]
    [else lst]))

;Funcion auxiliar para verify-vars
(define (jiyu-hensu expr)
      (nanopass-case (L8 Expr) expr
                     [,x `(,x)]
                     [(quot ,c) '()]
                     [(begin ,e* ...,e) (union (jiyu-hensu e) (foldr union '() (map jiyu-hensu e*)))]
                     [(if ,e0 ,e1 ,e2) (union (union (jiyu-hensu e0) (jiyu-hensu e1)) (jiyu-hensu e2))]
                     [(lambda ([,x* ,t*] ...) ,body) (remv* (jiyu-hensu body) x*)]
                     [(let ([,x ,t ,e*]) ,body) (rmvl (union (jiyu-hensu body) (jiyu-hensu e*))  `,x)]
                     [(letrec ([,x ,t ,e*]) ,body) (rmvl (union (jiyu-hensu body) (jiyu-hensu e*) `,x))]
                     [(letfun ([,x ,t ,e*]) ,body) (rmvl (union (jiyu-hensu body) (jiyu-hensu e*) `,x))]
                     [(primapp ,pr ,e* ...) (foldr union '() (map jiyu-hensu e*))]
                     [(list ,e* ...) (foldr union '() (map (jiyu-hensu e*)))]
                     [else expr]))

;Proceso verify-vars
(define-pass verify-vars : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [,x (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                           `,ir
                                           (error (string-append "free var " (symbol->string (car lst))))))]
        [(quot ,c) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                  `,ir
                                                  (error (string-append "free var " (symbol->string (car lst))))))]
        [(begin ,e* ...,e) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                          `,ir
                                                          (error (string-append "free var " (symbol->string (car lst))))))]
        [(primapp ,pr ,[e*] ...) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                                `,ir
                                                                (error (string-append "free var " (symbol->string (car lst))))))]
        [(if ,e0 ,e1 ,e2) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                         `,ir
                                                         (error (string-append "free var " (symbol->string (car lst))))))]
        [(lambda ([,x* ,t*] ...) ,body) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                                       `,ir
                                                                       (error (string-append "free var " (symbol->string (car lst))))))]
        [(let ([,x* ,t* ,e*]) ,body) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                                    `,ir
                                                                    (error (string-append "free var " (symbol->string (car lst))))))]
        [(letrec ([,x* ,t* ,e*]) ,body) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                                       `,ir
                                                                       (error (string-append "free var " (symbol->string (car lst))))))]
        [(list ,e* ...) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                       `,ir
                                                       (error (append "free var" (car lst)))))]
        [(letfun ([,x ,t ,e]) ,body) (let([lst (jiyu-hensu ir)])(if (empty? lst)
                                                                    `,ir
                                                                    (error (string-append "free var " (symbol->string (car lst))))))]))

;;-----------------------------------------------Practica 5
;; Función que verifica si dos tipos son unificables, para mas detalle consultar 
;; la especificación.
(define (unify t1 t2)
	(if (and (type? t1) (type? t2))
		(cond 
			[(equal? t1 t2) #t]
			[(and (equal? 'List t1) (list? t2)) (equal? (car t2) 'List)]
			[(and (equal? 'List t2) (list? t1)) (equal? (car t1) 'List)]
			[(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)) (unify (caddr t1) (caddr t2)))]
			[else #f])
		(error "Se esperaban 2 tipos")))

;; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
	(if (equal? (car lst) 'List)
		(part (cdr lst))
		(car lst)))

;; Procesos
; Proceso 1
(define-pass curry : L8 (ir) -> L9 ()
  (definitions
    (define (curryl x* t* body)
      (cond
        [(null? x*) (unparse-L8 body)]
        [else `(lambda ([,(car x*) ,(car t*)]) ,(curryl (cdr x*) (cdr t*) body))])))
  (Expr : Expr (ir) -> Expr()
        [(lambda ([,x* ,t*] ...) ,body) (cond
                                          [(list? x*) `(lambda ([,(car x*) ,(car t*)]) ,(parser-L9(curryl (cdr x*) (cdr t*) body)))]
                                          [else `(lambda ([,x* ,t*]) ,body)])]
        [else `,ir]))

; Proceso 2
(define-pass type-const : L9 (ir) -> L10 ()
  (definitions
    (define (whatype? t)
      (cond
        [(integer? t) 'Int]
        [(char? t) 'Char]
        [(boolean? t) 'Bool])))
  (Expr : Expr (ir) -> Expr()
        [(quot ,c) `(const ,(whatype? c) ,c)]
        [else `,ir]))

; Proceso 3
(define-pass type-infer : L10 (ir) -> L10 ()
  (Expr : Expr (ir) -> Expr()
        [(letrec ([,x ,t ,e]) ,body) (let ([type (J e '())])
                                       (if(equal? t 'Lambda)
                                          `(letrec ([,x ,type ,e]) ,body)
                                          `(letrec ([,x ,t ,e]) ,body)))]
        [(let ([,x ,t ,e]) ,body) (let ([type (J e '())])
                                    (if(equal? type 'List)
                                       `(let ([,x ,t ,e]) ,body)
                                       `(let ([,x ,type ,e]) ,body)))]
        [else `,ir]))

; Funciones Auxiliares para el algoritmo J
(define (lookup x ctx)
  (cond
    [(null? ctx) (error "Variable Libre")]
    [else (if (equal? x (caar ctx))
              (cdr(car ctx))
              (lookup x (cdr ctx)))]))

(define (num-primitive? x)
  (memq x '(+ - * /)))

(define (lst-primitive? x)
  (memq x '(length car cdr)))

(define (k-type? x) (if (list? x) 
	(let* (
		[f (car x)]
		[s (cadr x)]
		[t (caddr x)]) t) x))

;; Algoritmo J
(define (J expr ctx)
  (nanopass-case(L10 Expr) expr
                [,x (lookup x ctx)]
                [(const ,t ,c) `,t]
                [(list) 'List]
                [(list ,e* ...) (let* ([types (map (λ(x) (J x ctx)) e*)]
                                       [t (part types)]
                                       [eqt (map (λ(x) (unify t x)) types)]) (if (memq #f eqt)
                                                                                 (error "Lista Homogeneas.")
                                                                                 `(List of ,t)))]
                [(if ,e0 ,e1 ,e2) (let* ([type1 (J e1 ctx)]
                                         [type2 (J e2 ctx)]) (if (unify type1 type2)
                                                                `,type1
                                                                (error "No coinciden los tipos.")))]
                [(primapp ,pr ,e* ...) (cond
                                         [(num-primitive? pr) (let* ([type1 (J (car e*) ctx)]
                                                                     [type2 (J (car(cdr e*)) ctx)])
                                                                (if (or (not(equal? type1 'Int)) (not(equal? type2 'Int)))
                                                                    (error "Mal tipo")
                                                                    'Int))]
                                         [(lst-primitive? pr) (cond
                                                                [(equal? pr 'car) (let ([types (map (λ(x) (J x ctx)) e*)])
                                                                                    (k-type? (car types)))]
                                                                [(equal? pr 'length) (let ([types (map (λ(x) (J x ctx)) e*)])
                                                                                    'Int)]
                                                                [(equal? pr 'cdr) (let* ([types (map (λ(x) (J x ctx)) e*)]
                                                                                         [un (unparse-L10 (car e*))])
                                                                                    (cond
                                                                                      [(null? (cddr un)) `(List of)]
                                                                                      [else `(List of ,(k-type? (car types)))]))])])]
                [(lambda ([,x ,t]) ,body) (let* ([type1 (cons x t)]
                                                 [new-ctx (append ctx `,(list type1))])
                                            `(,t → ,(J body new-ctx)))]
                [(letfun ([,x ,t ,e]) ,body) (let* ([type1 (cons x t)]
                                                    [new-ctx (append ctx `,(list type1))]
                                                    [type-e (J e ctx)]
                                                    [type-b (J body new-ctx)])
                                               (if (and (unify t type-e) (equal? (cadr t) '→))
                                                   `,type-b
                                                   (error "No coinciden los tipos.")))]
                [(letrec ([,x ,t ,e]) ,body) (let* ([type1 (cons x t)]
                                                    [new-ctx (append ctx `,(list type1))]
                                                    [type-e (J e new-ctx)]
                                                    [type-b (J body new-ctx)])
                                               (if(unify t type-e)
                                                  `,type-b
                                                  (error "No coinciden los tipos.")))]
                [(let ([,x ,t ,e]) ,body) (let* ([type1 (cons x t)]
                                                 [new-ctx (append ctx `,(list type1))]
                                                 [type-e (J e ctx)]
                                                 [type-b (J body new-ctx)])
                                            (if(unify t type-e)
                                               `,type-b
                                               (error "No coinciden los tipos.")))]
                [(begin ,e* ... ,e) (let ([type1 (J e ctx)])
                                      `,type1)]))

;;------------------------------------------------------------Practica 6
;; Funcion Auxiliar para el primer Ejercicio
(define (make-lambda lst body)
  (nanopass-case(L10 Expr) body
                [(lambda ([,x ,t]) ,body) (make-lambda (append lst `([,x ,t])) body)]
                [else `(lambda ,lst ,(unparse-L10 body))]))

;; Ejercicio 1
(define-pass uncurry : L10 (ir) -> L11 ()
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t]) ,body) `,(parser-L11 (make-lambda '() ir))]
        [else (parser-L11 (unparse-L10 ir))]))

;; Algoritmo J
(define (J-1 expr ctx)
  (nanopass-case(L11 Expr) expr
                [,x (lookup x ctx)]
                [(const ,t ,c) `,t]
                [(list) 'List]
                [(list ,e* ...) (let* ([types (map (λ(x) (J-1 x ctx)) e*)]
                                       [t (part types)]
                                       [eqt (map (λ(x) (unify t x)) types)]) (if (memq #f eqt)
                                                                                 (error "Lista Homogeneas.")
                                                                                 `(List of ,t)))]
                [(if ,e0 ,e1 ,e2) (let* ([type1 (J-1 e1 ctx)]
                                         [type2 (J-1 e2 ctx)]) (if (unify type1 type2)
                                                                `,type1
                                                                (error "No coinciden los tipos.")))]
                [(primapp ,pr ,e* ...) (cond
                                         [(num-primitive? pr) (let* ([type1 (J-1 (car e*) ctx)]
                                                                     [type2 (J-1 (car(cdr e*)) ctx)])
                                                                (if (or (not(equal? type1 'Int)) (not(equal? type2 'Int)))
                                                                    (error "Mal tipo")
                                                                    'Int))]
                                         [(lst-primitive? pr) (cond
                                                                [(equal? pr 'car) (let ([types (map (λ(x) (J-1 x ctx)) e*)])
                                                                                    (k-type? (car types)))]
                                                                [(equal? pr 'length) (let ([types (map (λ(x) (J-1 x ctx)) e*)])
                                                                                    'Int)]
                                                                [(equal? pr 'cdr) (let* ([types (map (λ(x) (J-1 x ctx)) e*)]
                                                                                         [un (unparse-L11 (car e*))])
                                                                                    (cond
                                                                                      [(null? (cddr un)) `(List of)]
                                                                                      [else `(List of ,(k-type? (car types)))]))])])]
                [(lambda ([,x ,t]) ,body) (let* ([type1 (cons x t)]
                                                 [new-ctx (append ctx `,(list type1))])
                                            `(,t → ,(J-1 body new-ctx)))]
                [(letfun ([,x ,t ,e]) ,body) (let* ([type1 (cons x t)]
                                                    [new-ctx (append ctx `,(list type1))]
                                                    [type-e (J-1 e ctx)]
                                                    [type-b (J-1 body new-ctx)])
                                               (if (and (unify t type-e) (equal? (cadr t) '→))
                                                   `,type-b
                                                   (error "No coinciden los tipos.")))]
                [(letrec ([,x ,t ,e]) ,body) (let* ([type1 (cons x t)]
                                                    [new-ctx (append ctx `,(list type1))]
                                                    [type-e (J-1 e new-ctx)]
                                                    [type-b (J-1 body new-ctx)])
                                               (if(unify t type-e)
                                                  `,type-b
                                                  (error "No coinciden los tipos.")))]
                [(let ([,x ,t ,e]) ,body) (let* ([type1 (cons x t)]
                                                 [new-ctx (append ctx `,(list type1))]
                                                 [type-e (J-1 e ctx)]
                                                 [type-b (J-1 body new-ctx)])
                                            (if(unify t type-e)
                                               `,type-b
                                               (error "No coinciden los tipos.")))]
                [(begin ,e* ... ,e) (let ([type1 (J e ctx)])
                                      `,type1)]))
(define count-1 0)
(define (new-name)
      (begin
        (define str (string-append "x" (number->string count)))
        (set! count-1 (+ count-1 1))
        (string->symbol str)))

(define (make-bind t v)
  (cons t v))

(define ht-1 (make-hash))

;; Ejercicio 2
(define (symbol-table-var expr)
  (nanopass-case(L11 Expr) expr
                [,x `,x]
                [(const ,t ,c) (hash-set! ht-1 (new-name) (make-bind `,t (list (unparse-L11 expr))))]
                [(list ,e* ...) (begin
                                  (map(λ(x) (symbol-table-var x)) e*)
                                  (hash-set! ht-1 (new-name) (make-bind (J expr '()) (list (unparse-L11 expr)))))]
                [(if ,e0 ,e1 ,e2) (begin
                                    (symbol-table-var e0)
                                    (symbol-table-var e1)
                                    (symbol-table-var e2)
                                    (hash-set! ht-1 (new-name) (make-bind (J expr '()) (list (unparse-L11 expr)))))]
                [(primapp ,pr ,e* ...) (begin
                                         (symbol-table-var (car e*))
                                         (symbol-table-var (car(cdr e*)))
                                         (hash-set! ht-1 (new-name) (make-bind (J expr '()) (list (unparse-L11 expr)))))]
                [(lambda ([,x ,t] ...) ,body) `,body]
                [(letfun ([,x ,t ,e]) ,body) (begin
                                               (hash-set! ht-1 `,x (make-bind `,t (list (unparse-L11 e))))
                                               (let* ([type (cons x t)]
                                                      [new-ctx (append '() `,(list type))])
                                                 (hash-set! ht-1 (new-name) (make-bind (J body new-ctx)
                                                                                     (list (unparse-L11 body))))))]
                [(letrec ([,x ,t ,e]) ,body) (begin
                                               (hash-set! ht-1 `,x (make-bind `,t (list (unparse-L11 e))))
                                               (let* ([type (cons x t)]
                                                      [new-ctx (append '() `,(list type))])
                                                 (hash-set! ht-1 (new-name) (make-bind (J body new-ctx)
                                                                                     (list (unparse-L11 body))))))]
                [(let ([,x ,t ,e]) ,body) (begin
                                               (hash-set! ht-1 `,x (make-bind `,t (list (unparse-L11 e))))
                                               (let* ([type (cons x t)]
                                                      [new-ctx (append '() `,(list type))])
                                                 (hash-set! ht-1 (new-name) (make-bind (J body new-ctx)
                                                                                     (list (unparse-L11 body))))))]
                [(begin ,e* ... ,e) (begin
                                      (map(λ(x) (symbol-table-var x)) e*)
                                      (hash-set! ht-1 (new-name) (make-bind (J e '()) (list (unparse-L11 e))))
                                      (hash-set! ht-1 (new-name) (make-bind (J expr '()) (list (unparse-L11 expr)))))]))

(define-pass assigment : L11 (ir) -> L12 ()
  (Expr : Expr(ir) -> Expr()
        [(let ([,x ,t ,e]) ,body) (begin
                                    (symbol-table-var ir)
                                    `(let ,body))]
        [(letrec ([,x ,t ,e]) ,body) (begin
                                       (symbol-table-var ir)
                                       `(letrec ,body))]
        [(letfun ([,x ,t ,e]) ,body) (begin
                                       (symbol-table-var ir)
                                       `(letfun ,body))]))

(define (back-end str)
  (eta-expand
   (remove-arit-operators
    (remove-logical-operators
     (make-explicit
      (remove-string
       (remove-one-armed-if(parser-LF str))))))))