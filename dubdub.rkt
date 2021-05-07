#lang racket #| * CSC324 Fall 2019: Assignment 1 * |#
#|
Module: dubdub
Description: Assignment 1: A More Featureful Interpreter
Copyright: (c)University of Toronto, University of Toronto Mississauga 
               CSC324 Principles of Programming Languages, Fall 2019

The assignment handout can be found at

    https://www.cs.toronto.edu/~lczhang/324/files/a1.pdf

Please see the assignment guidelines at 

    https://www.cs.toronto.edu/~lczhang/324/homework.html
|#

(provide run-interpreter)

(require "dubdub_errors.rkt")


;-----------------------------------------------------------------------------------------
; Main functions (skeleton provided in starter code)
;-----------------------------------------------------------------------------------------
#|
(run-interpreter prog) -> any
  prog: datum?
    A syntactically-valid Dubdub program.

  Evaluates the Dubdub program and returns its value, or raises an error if the program is
  not semantically valid.
|#
(define (run-interpreter prog)
  (interpret (create-env (hash) (reverse (rest (reverse prog)))) (last prog)))

#|
(create-env env prog) -> any
  prog: datum?
    A syntactically-valid Dubdub program.
  env: hash?
    Global hash table.

  Evaluates the required hash table for the program.
|#
(define (create-env env prog)
  (if (equal? '() prog) env
      (create-env (interpret env (first prog)) (rest prog))))

#|
(call_builtin env expr) -> any
  expr: datum?
    A syntactically-valid Dubdub builtin function call.

  Returns the value of the Dubdub expression.
|#
(define (call_builtin env expr)
  (cond
    [(equal? (first expr) '+) (adder env (rest expr))]
    [(equal? (first expr) '<) (< (interpret env (second expr)) (interpret env (third expr)))]
    [(equal? (first expr) 'equal?) (equal? (interpret env (second expr)) (interpret env (third expr)))]
    [(equal? (first expr) 'integer?) (integer? (interpret env (second expr)))]
    [(equal? (first expr) 'boolean?) (boolean? (interpret env (second expr)))]
    [(equal? (first expr) 'procedure?) (list? (interpret env (second expr)))]))

#|
(adder env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.
  elements: list?
    Elements to add.

  Returns the total of elements.
|#
(define (adder env elements)
  (if (equal? elements '()) 0
      (+ (interpret env (first elements)) (adder env (rest elements)))))

#|
(create_closure env expr) -> any

  Returns closure as a list.
|#
(define (create_closure env expr)
  (let*
      ([params (second (first expr))]
       [values (rest expr)]
       [new_hash (create_hash params values env (hash))])
    (list 'closure (first expr) new_hash)))

#|
(create_hash params values env fenv) -> any
  params: list?
    Parameters in lambda expression.
  values: list?
    Rest of lambda function call, a list of values for new_hash.
  fenv: hash?
    Required hash for closure.

  Returns the hash for given params and values using previous env.
|#
(define (create_hash params values env fenv)
  (if (equal? values '()) fenv
      (if (hash-has-key? fenv (first params)) (create_hash (rest params) values env fenv)
          (create_hash (rest params) (rest values) env (hash-set fenv (first params) (interpret env (first values)))))))

#|
(duplicate_hash env fenv keys) -> any
  env: hash?
    The environment with which to evaluate the expression.
  keys: list?
    A list of keys in env.

  Returns a new fenv adding all the elemnts in env to it.
|#
(define (duplicate_hash keys env fenv)
  (if (equal? keys '()) fenv
      (duplicate_hash (rest keys) env (hash-set fenv (first keys) (hash-ref env (first keys))))))

#|
(call_function env params values closure) -> any
  env: hash?
    The environment with which to evaluate the expression.

  When a function call is envoked, interprets closure and returns the result.
|#
(define (call_function env params values closure)
  (if (and (equal? params '()) (not (equal? values '()))) (report-error 'arity-mismatch (+ (length values) (length (second (second closure)))) (length (second (second closure))))
      (if (equal? values '()) (interpret env closure)
          (if (hash-has-key? (third closure) (first params)) (call_function env (rest params) values (list 'closure (second closure) (third closure)))
              (call_function env (rest params) (rest values) (list 'closure (second closure) (hash-set (third closure) (first params) (first values))))))))

#|
(interpret env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.
  expr: datum?
    A syntactically-valid Dubdub expression.

  Returns the value of the Dubdub expression under the given environment.
|#
(define (interpret env expr)
  (cond
    [(integer? expr) expr]
    [(boolean? expr) expr]
    [(builtin? expr) expr]
    [(symbol? expr) (if (hash-has-key? env expr) (hash-ref env expr) (report-error 'unbound-name expr))]
    [(builtin? (first expr)) (call_builtin env expr)]
    [(hash-has-key? env (first expr)) (if (builtin? (hash-ref env (first expr))) (interpret env (append (list (hash-ref env (first expr))) (rest expr))) (let*
                                          ([closure (hash-ref env (first expr))]
                                           [params (second (second closure))]
                                           [values (rest expr)])
                                        (if (hash-has-key? env (list (first expr) 'contract))
                                            (let*
                                                ([conditions (hash-ref env (list (first expr) 'contract))]
                                                 [preconditions (reverse (rest (rest (reverse conditions))))]
                                                 [postcondition (last conditions)])
                                              (call-function-contract env params values closure preconditions postcondition))
                                            (call_function env params values closure))))]
    [(equal? (first expr) 'closure) (check-parameters env expr)]
    [(equal? (first expr) 'lambda) (list 'closure expr (hash))]
    [(equal? (first expr) 'define) (if (hash-has-key? env (second expr)) (report-error 'duplicate-name (second expr)) (hash-set (contract-currying env expr) (second expr) (interpret env (third expr))))]
    [(equal? (first expr) 'define-contract) (check-contract env expr)]
    [(and (list? (first expr)) (equal? (first (first expr)) 'lambda)) (if (equal? (length (second (first expr))) (length (rest expr))) (interpret env (create_closure env expr)) (if (< (length (second (first expr))) (length (rest expr))) (report-error 'arity-mismatch (length (rest expr)) (length (second (first expr)))) (create_closure env expr)))]
    [(list? (first expr)) (interpret env (build-closure env expr))]
    [else (report-error 'not-a-function expr)]
    ))

#|
(check-contract env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.

  Checks the contract for invalid definitions.
|#
(define (check-contract env expr)
  (let*
      ([preconditions (reverse (rest (rest (reverse (third expr)))))]
       [arrow (second (reverse (third expr)))]
       [postcondition (last (third expr))])
    (if (equal? arrow '->) 
        (if (check-contract-pre-post env preconditions)
            (if (check-contract-pre-post env (list postcondition)) (if (hash-has-key? env (list (second expr) 'contract)) (report-error 'duplicate-name (second expr)) (hash-set env (list (second expr) 'contract) (third expr)))
                (report-error 'invalid-contract (second expr))) (report-error 'invalid-contract (second expr))) (report-error 'invalid-contract (second expr)))))

#|
(check-contract-pre-post env conditions) -> any
  env: hash?
    The environment with which to evaluate the expression.

  Checks the contract for invalid definitions.
|#
(define (check-contract-pre-post env conditions)
  (if (equal? '() conditions) #t
      (if (builtin? (first conditions)) (check-contract-pre-post env (rest conditions))
          #f)))

#|
(contract-currying env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.

  Returns a hash needed for currying.
|#
(define (contract-currying env expr)
  (if (interpret env (list 'procedure? (interpret env (third expr))))
      (if (or (equal? (first (third expr)) 'lambda) (not (hash-has-key? env (list (first (third expr)) 'contract)))) env
          (hash-set env (list (second expr) 'contract) (hash-ref env (list (first (third expr)) 'contract))))
      env))

#|
(check-precondition env parameter value precondition) -> any
  env: hash?
    The environment with which to evaluate the expression.
  precondition: builtin?
    Preconditions to check.

  Checks if the given precondition is satisfied. Returns true if satisfied.
|#
(define (check-precondition env parameter value precondition)
  (if (equal? precondition 'any) #t
      (interpret env (list precondition value))))

#|
(call-function-contract env parameters values closure preconditions postcondition) -> any
  env: hash?
    The environment with which to evaluate the expression.
  preconditions: list?
    The list of preconditions in the contract.
  postcondition: builtin?
    The last element in the conditions list.

  Calls a function that has a contract.
|#
(define (call-function-contract env parameters values closure preconditions postcondition)
  (if (and (equal? parameters '()) (not (equal? values '()))) (report-error 'arity-mismatch (+ (length values) (length (second (second closure)))) (length (second (second closure))))
      (if (equal? '() values)
          (cond
            [(equal? (length (second (second closure))) (length (hash-keys (third closure)))) (if (equal? postcondition 'any) (interpret env closure)
                                                                                                  (if (interpret env (list postcondition (interpret env closure))) (interpret env closure)
                                                                                                      (report-error 'contract-violation)))]
            [(> (length (second (second closure))) (length (hash-keys (third closure)))) closure])
          (if (hash-has-key? (third closure) (first parameters)) (call-function-contract env (rest parameters) values (list 'closure (second closure) (third closure)) (rest preconditions) postcondition)
              (if (check-precondition env (first parameters) (first values) (first preconditions))
                  (call-function-contract env (rest parameters) (rest values) (list 'closure (second closure) (hash-set (third closure) (first parameters) (first values))) (rest preconditions) postcondition)
                  (report-error 'contract-violation))))))

#|
(check-parameters env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.
  expr: datum?
    A syntactically-valid Dubdub expression.

  Checks the number of parameters and creates a closure if parameters are less than values for currying, evaluates otherwise.
|#
(define (check-parameters env expr)
  (cond
    [(equal? (length (second (second expr))) (length (hash-keys (third expr)))) (interpret (duplicate_hash (hash-keys env) env (third expr)) (third (second expr)))]
    [(> (length (second (second expr))) (length (hash-keys (third expr)))) expr]))

(define (build-closure env expr)
  (if (and (list? (first expr)) (not (equal? (first (first expr)) 'lambda)))
      (append (build-closure env (first expr)) (get-value env (rest expr)))
      (append (list (first expr)) (get-value env (rest expr)))))

(define (get-value env expr)
  (if (null? expr)
      null
      (append (list (interpret env (first expr))) (get-value env (rest expr)))))
;-----------------------------------------------------------------------------------------
; Helpers: Builtins and closures
;-----------------------------------------------------------------------------------------
; A hash mapping symbols for Dubdub builtin functions to their corresponding Racket value.
(define builtins
  (hash
   '+ +
   'equal? equal?
   '< <
   'integer? integer?
   'boolean? boolean?
   ; Note: You'll almost certainly need to replace procedure? here to properly return #t
   ; when given your closure data structure at the end of Task 1!
   'procedure? procedure?
   ))

; Returns whether a given symbol refers to a builtin Dubdub function.
(define (builtin? identifier) (hash-has-key? builtins identifier))

#|
Starter definition for a closure "struct". Racket structs behave similarly to
C structs (contain fields but no methods or encapsulation).
Read more at https://docs.racket-lang.org/guide/define-struct.html.

You can and should modify this as necessary. If you're having trouble working with
Racket structs, feel free to switch this implementation to use a list/hash instead.
|#
(struct closure (params body)) ;We used a list instead of a struct for closures.