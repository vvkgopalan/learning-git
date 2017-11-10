#lang racket

(provide 
         entry entry-key entry-value entry?
         bnot bnot-arg bnot?
         band band-arg1 band-arg2 band?
         bor bor-arg1 bor-arg2 bor?
         tt tt-vars tt-rows tt?
	 hours
         lookup unique-keys?
         boolean-exp? type-of
	 all-vars
	 eval-in-env
	 all-combs
	 truth-table	 	 	 
	 satisfiable? equivalent?
	 find-exp
         substitute-in
         match)

; Please do not modify lines above this one.

; ****************************************************************
; CS 201b HW #4  DUE 11:59 pm Sunday, October 22, 2017
; using the submit command on the Zoo.
; ****************************************************************
; Name: Vivek Gopalan
; Email address: vivek.gopalan@yale.edu
; ****************************************************************
; ** problem 0 ** (1 easy point)
; Please modify the following definition to reflect the number of
; hours you spent on this assignment.

(define hours 3.5)

; ****************************************************************
; Unless the problem specifies otherwise:
; * You may solve the problem using any method 
; and any Racket constructs, except mutators (set! and its relatives.)
; * You may write auxiliary procedure(s) in addition to
; the one(s) specified in the problem.  Please include
; a comment for each one explaining its input and results.

; The topics of this assignment are as follows.
; Racket: deep recursion on a recursively defined data structure.
; Computer Science: Boolean functions, expressions, environments,
; truth tables, satisfiability, equivalence.

; You might also find uses for the special form: case.

; ****************************************************************
; We define a table as a list of entries,
; where each entry is given by the following structure.

(struct entry (key value) #:transparent)

; Recall that a struct defines a constructor, selector(s), and a type predicate.
; In this case, the constructor is entry, the selectors are
; entry-key and entry-value, and the type predicate is entry?.

; Here are two examples of tables.

(define test1
  (list
   (entry "second" 2)
   (entry "first" 1)
   (entry "fifth" 5)))

(define test2
  (list
   (entry 'x 0)
   (entry 'z 1)
   (entry 'y 1)
   (entry 'z 0)))

; ****************************************************************
; ** problem 1 ** (9 points)
; Write two procedures to deal with tables as follows.

; (lookup key table)
; (unique-keys? table)

; (lookup key table)
; returns #f if no entry in the table has a key equal? to key
; otherwise, returns the value of the first entry whose key is equal? to key.

; (unique-keys? table)
; returns #t if all the entries of table have keys that are pairwise
; not equal? and #f otherwise.

; Examples
;> (lookup "first" test1)
;1
;> (lookup "third" test1)
;#f
;> (lookup 'z test2)
;1
;> (unique-keys? test1)
;#t
;> (unique-keys? test2)
;#f
;>
; ****************************************************************

(define (lookup key table)
  (if (and (not (empty? table))(equal? (entry-key (car table)) key))
      (entry-value (car table))
      (if (or (empty? table)(empty? (cdr table)))
          #f
          (lookup key (cdr table)))))

(define (unique-keys? table)
  (if (and (not (empty? table))(equal? (lookup (entry-key (car table)) table)
              (lookup (entry-key (car table)) (reverse table))))
      (if (empty? (cdr table))
          #t
          (unique-keys? (cdr table)))
      #f))

; ****************************************************************
; Our representation of Boolean expressions will use the following
; struct definitions.  Note that the transparent attribute allows
; the contents of a structure to be printed out, and allows two
; structures to be compared for content using equal?

(struct bnot (arg) #:transparent)
(struct band (arg1 arg2) #:transparent)
(struct bor (arg1 arg2) #:transparent)

; We recursively define a representation of Boolean expressions as follows.

; 1) 0 and 1 represent the constants 0 and 1
; 2) Racket symbols represent variables (for example, 'x, 'y, 'z2)
; 3) If exp1 and exp2 represent Boolean expressions, then
;    (bnot exp1) represents the NOT of exp1
;    (band exp1 exp2) represents the AND of exp1 and exp2
;    (bor exp1 exp2) represents the OR of exp1 and exp2

; Some examples of Boolean expressions follow.

(define exp0 (bnot 0))
(define exp1 (bor 'x 'y))
(define exp2 (band 'y 'z))
(define exp3 (band 'w (bor (bnot 'x) 0)))
(define exp4 (bor 'x (bnot 'x)))
(define exp5 (band (bor 'x (bnot 'y)) (bnot (band 0 'z))))

; ****************************************************************
; ** problem 2 ** (10 points)
; Write two procedures

; (boolean-exp? exp)
; (type-of exp)

; (boolean-exp? exp) takes an arbitrary Racket value exp
; and tests to see whether it is a Boolean expression according
; to the definition above, returning #t if so and #f if not.

; (type-of exp)
; that takes a Boolean expression as defined above
; and returns its type as one of the symbols:
;   constant, variable, not, or, and
; Note that the type is determined by the top-level
; operation in case the expression is not a constant or variable.

; Recall that (number? exp) tests whether exp is a number,
; and (symbol? exp) tests whether exp is a symbol, and the
; structs bnot, band, and bor have type predicates bnot?, band?, and bor?

; Examples
;> (boolean-exp? 0)
;#t
;> (boolean-exp? 2)
;#f
;> (boolean-exp? exp0)
;#t
;> (boolean-exp? (band "hi" 'c))
;#f
;> (boolean-exp? (band 'x (bor 0 (bnot 1))))
;#t
;> (boolean-exp? (band 'x (bor 0 (bnot #t))))
;#f
;> (type-of 0)
;'constant
;> (type-of 'hi)
;'variable
;> (type-of (bnot (band 'x 0)))
;'not
;> (type-of (bor (band 'x 'y) (band 'x 'z)))
;'or
;> (type-of (band (bor 0 1) (bnot 'x)))
;'and
; ****************************************************************

(define (boolean-exp? exp)
  (cond
    [(or (equal? 0 exp) (equal? 1 exp)) #t]
    [(symbol? exp) #t]
    [(or (and (bor? exp)(boolean-exp? (bor-arg1 exp))(boolean-exp? (bor-arg2 exp)))
         (and (band? exp)(boolean-exp? (band-arg1 exp))(boolean-exp? (band-arg2 exp)))
         (and (bnot? exp) (boolean-exp? (bnot-arg exp)))) #t]
    [else #f]
    ))

(define (type-of exp)
  (if (struct? exp)
      (cond
        [(bnot? exp) 'not]
        [(bor? exp) 'or]
        [(band? exp) 'and]
        )
      (cond
        [(symbol? exp) 'variable]
        [(or (equal? exp 1)(equal? exp 0))'constant]
        )))

; ****************************************************************
; ** problem 3 ** (10 points)
; Write a procedure

; (all-vars exp)

; that takes a Boolean expression exp 
; and makes a list containing all the variables
; that occur in exp.  The list should not contain duplicates,
; and should have the variables in the order of their
; first appearance in exp (scanning left to right.)

; Hint: selectors, type-of and deep recursion on the structure 
; of Boolean expressions.  Note that there is a Racket procedure
; remove-duplicates.

; Examples
;> (all-vars 0)
;'()
;> (all-vars (bnot (band 'x (band 'y (bor 'x 'z)))))
;'(x y z)
;> (all-vars (band 1 (bor 0 (bnot 'u))))
;'(u)
;> (all-vars (band (band 'x 'y) (band 'y 'x)))
;'(x y)
;> (all-vars (bor (bor (bor 'c 'b) (bor 'a 'b)) 'c))
;'(c b a)
;> 
; ****************************************************************

(define (all-vars exp)
  (if (equal? (type-of exp) 'constant)
      '()
      ;if its a boolean expression thats not a number or a constant, calls the helper method
      (if (equal? (type-of exp) 'variable)
          (list exp)
          ;remove duplicates and return list of all the variables
          (remove-duplicates (all-vars-helper exp)))))
(define (all-vars-helper exp)
  (cond
    ;if its a symbol within the exp, return the list of the symbol to be appended
    [(symbol? exp) (list exp)]
    [(band? exp)
     ;if its band and first is a var, check if 2nd is a var and append it
     ;else, append the result of the recursive calls on both boolean expressions.
     ;does the exact same things for bor and bnot (except 1 expression to evaluate for bnot)
                 (if (equal? (type-of (band-arg1 exp)) 'variable)
                     (append (list(band-arg1 exp)) (all-vars-helper (band-arg2 exp)))
                     (append (all-vars-helper (band-arg1 exp)) (all-vars-helper (band-arg2 exp))))]
    [(bor? exp)
                 (if (equal? (type-of (bor-arg1 exp)) 'variable)
                     (append (list(bor-arg1 exp)) (all-vars-helper (bor-arg2 exp)))
                     (append (all-vars-helper (bor-arg1 exp)) (all-vars-helper (bor-arg2 exp))))]
    [(bnot? exp) (append (all-vars-helper (bnot-arg exp)))]
    [else '()]
    )
  )

    

; ****************************************************************
; We represent an environment as a table each entry of which
; has a key that is a Racket symbol and a value that is 0 or 1,
; which specifies the truth value of that variable in the environment.
; For example:

(define environ1
  (list
   (entry 'x 0) (entry 'y 1) (entry 'z 0)))
  
(define environ2
  (list
   (entry 'u 0) (entry 'x 1) (entry 'w 1) (entry 'y 0) (entry 'z 1)))

; ****************************************************************
; ** problem 4 ** (10 points)
; Write a procedure 

; (eval-in-env exp env)

; that takes a Boolean expression exp and an environment env
; (represented as described above) and returns 0 or 1 giving 
; the value of the expression in the environment.

; If the Boolean expression contains variables that do not
; occur in the environment, (eval-in-env exp env) should
; return the symbol: 'unspecified-variable.
; (You may want to check for this condition first.)

; Hint: deep recursion on the structure of Boolean expressions
; along with argument selectors and type-of.

; Examples
;> (eval-in-env 1 environ1)
;1
;> (eval-in-env (bor 0 0) '())
;0
;> (eval-in-env 'x environ1)
;0
;> (eval-in-env 'x environ2)
;1
;> (eval-in-env (bnot 'z) environ1)
;1
;> (eval-in-env (bor 'y (bnot 'x)) environ2)
;0
;> (eval-in-env (band (band (bor 'u 'x) (bor 'w 0)) (bnot (band 'y 'z))) environ2)
;1
;> (eval-in-env exp5 environ1)
;0
;> (eval-in-env (band 'y (bor 'x 'u)) (list (entry 'x 0) (entry 'y 1)))
;'unspecified-variable
;>
; ****************************************************************

(define (eval-in-env exp env)
  (cond
    ;first few are simple test case checks
    [(and (symbol? exp)(empty? env)) 'unspecified-variable]
    [(number? exp) exp]
    [(symbol? exp) (lookup exp env)]
    ;next three are for bexps - each one calls a helper function taking in each argument as a recursive call
    [(band? exp) (andbool (eval-in-env (band-arg1 exp) env)(eval-in-env (band-arg2 exp) env))]
    [(bor? exp) (orbool (eval-in-env (bor-arg1 exp) env)(eval-in-env (bor-arg2 exp) env))]
    [(bnot? exp) (notbool (eval-in-env (bnot-arg exp) env))]
    [else 'unspecified-variable]
    )
  )
(define (andbool b1 b2)
  (cond
    [(or (not (number? b1))(not (number? b2))) 'unspecified-variable]
    ;if both var 1 and var 2 are 1, it returns 1 as the band is satisfied
    [(equal? (+ b1 b2) 2) 1]
    ;else returns 0 (false)
    [else 0]
    ))
(define (orbool b1 b2)
  (cond
    [(or (not (number? b1))(not (number? b2))) 'unspecified-variable]
    ;if either var 1 or var 2 are 1, returns 1, else returns 0
    [(> (+ b1 b2) 0) 1]
    [else 0]
    ))
(define (notbool b1)
  (cond
    [(not (number? b1)) 'unspecified-variable]
    ;does the not evaluation
    [(zero? b1) 1]
    [else 0]
    ))
                 

; ****************************************************************
; We define a truth table as represented by the following struct

(struct tt (vars rows) #:transparent)

; whose fields contain the following
; (1) a (possibly empty) list of n distinct variables, and
; (2) a table containing an entry for each combination of n 0's and 1's,
; whose key is a list of n 0's and 1's and whose value is the value (0 or 1)
; of the function represented by the truth table.

; Note that the entries in a truth table should be in increasing order of
; their keys, considered as binary numbers.

; Examples of truth tables for the expressions
; (bnot 'x), (band 'x 'y), (bor (bnot 'a) 'b) 
; and the function that is the XOR of 'u and 'v.

(define tt-not (tt '(x)
                   (list
                    (entry '(0) 1)
                    (entry '(1) 0))))

(define tt-and (tt '(x y)
                   (list 
                    (entry '(0 0) 0)
                    (entry '(0 1) 0)
                    (entry '(1 0) 0)
                    (entry '(1 1) 1))))
                    
 
(define tt-imp (tt '(a b)
                   (list
                    (entry '(0 0) 1)
                    (entry '(0 1) 1)
                    (entry '(1 0) 0)
                    (entry '(1 1) 1))))
  
(define tt-xor (tt '(u v)
                   (list
                    (entry '(0 0) 0)
                    (entry '(0 1) 1)
                    (entry '(1 0) 1)
                    (entry '(1 1) 0))))

; Here is a truth table for a function of three arguments a, b, c.

(define tt-f1 (tt '(a b c)
                  (list
                   (entry '(0 0 0) 0)
                   (entry '(0 0 1) 0)
                   (entry '(0 1 0) 1)
                   (entry '(0 1 1) 1)
                   (entry '(1 0 0) 0)
                   (entry '(1 0 1) 1)
                   (entry '(1 1 0) 0)
                   (entry '(1 1 1) 1))))

; ****************************************************************
; ** problem 5 ** (10 points)
; Write a procedure 

; (all-combs n)

; that takes a non-negative integer n and creates the list of all 
; lists of n 0's or 1's in the *specific order* required for
; a truth table.  In other words, the lists, interpreted as binary numbers, 
; should be in increasing order.

; Hint: if a recursive call gives the correct answer
; for (all-combs 2), what needs to happen to it
; to give the correct answer for (all-combs 3)?
; (This may remind you of power-set from assignment #1.)

; Use let or let* to avoid recomputing the recursive call!

; Examples
;> (all-combs 0)
;'(())
;> (all-combs 1)
;'((0) (1))
;> (all-combs 2)
;'((0 0) (0 1) (1 0) (1 1))
;> (all-combs 3)
;'((0 0 0) (0 0 1) (0 1 0) (0 1 1) (1 0 0) (1 0 1) (1 1 0) (1 1 1))
;> 
; ****************************************************************

(define (all-combs n)
  ;calls helper method (I wrote two versions, one does it in one lambda expression and requires the list '(0 1)
  ;permute requires the list with two branches as it uses append as opposed to cons (I could have cons'd (list x), but as you will see, this is easier)
  (if (zero? n)
      ;if all-combs 0, return '(())
      '(())
      ;sorts to result in the order desired
      (sort (permute '((0) (1)) 1 n) #:key car <)))

(define (all-combs-helper lst n)
  (if (zero? n)
      '(())
      (append-map
       ;does it all in 1 lambda expression, cons 1 to the list and appends that to a list with 0 cons'd to each element and keeps recursing
       (lambda (x)
         (map (lambda (y) (flatten (cons x y))) lst)) (all-combs-helper lst (- n 1)))))

(define (permute lst num max)
  (cond
    ;if the number is equal to the intial n (now max, return the list)
    [(= num max) lst]
    ;else, permute the rest - this starts from the list '((0)(1)) and appends a 1 to each element in the list
    ;and appends it to a list which has the same process with 0's
    ;e.g. would become '((0 1)(1 1)(1 0)(1 1))
    [(< num max)
     (permute (append (map (lambda (x) (cons 0 x)) lst)
                         (map (lambda (x) (cons 1 x)) lst)) (+ num 1) max)]))

; ****************************************************************
; ** problem 6 ** (10 points)
; Write a procedure

; (truth-table exp)

; that takes a Boolean expression exp and returns the truth table for exp
; where the variables for the table are extracted from exp using all-vars, 
; and the function value for each row is obtained by evaluating exp 
; in the corresponding environment.  Notice that all-vars specifies
; the order of variables for the truth table.

; Examples:
;> (truth-table exp0)
;(tt '() (list (entry '() 1)))
;> (truth-table exp1)
;(tt
; '(x y)
; (list (entry '(0 0) 0) (entry '(0 1) 1) (entry '(1 0) 1) (entry '(1 1) 1)))
;> (truth-table exp5)
;(tt
; '(x y z)
; (list
;  (entry '(0 0 0) 1)
;  (entry '(0 0 1) 1)
;  (entry '(0 1 0) 0)
;  (entry '(0 1 1) 0)
;  (entry '(1 0 0) 1)
;  (entry '(1 0 1) 1)
;  (entry '(1 1 0) 1)
;  (entry '(1 1 1) 1)))
;> 
; ****************************************************************

(define (truth-table exp)
  (if (empty? (all-vars exp))
      ;if the expression is empty, it gives the empty truth table
      (tt (all-vars exp) (list (entry '() (eval-in-env exp 1))))
      ;else, gives an truth table by evaluating all the values for all-combs of that length
      ;calls entries to generate each individual entry
      (tt (all-vars exp) (entries exp (all-combs (length (all-vars exp))) (all-vars exp)))))
(define (entries exp lst variables)
  (cond
    [(empty? lst) '()]
    ;makes a list of entries
    ;for each entry, its given the values for all the vars e.g. '('x 'z) '(1 1)
    ;calls environment to find the specific value for that line
    [else (cons (entry (car lst) (eval-in-env exp (environment (car lst) variables)))
                (entries exp (cdr lst) variables))]))
(define (environment vals variables)
  (cond
    [(empty? vals) '()]
    [else (cons (entry (car variables) (car vals)) (environment (cdr vals) (cdr variables)))]))

; ****************************************************************
; ** problem 7 ** (10 points)
; Write two procedures

; (satisfiable? exp)
; (equivalent? exp1 exp2)

; (satisfiable? exp)
; takes one Boolean expression exp and
; returns #t if exp is satisfiable and #f otherwise.

; (equivalent? exp1 exp2)
; takes two Boolean expressions exp1 and exp2
; and returns #t if they are equivalent and #f if they
; are not equivalent.

; A Boolean expression is satisfiable if there exists an environment
; in which its value is 1.  Two Boolean expressions are equivalent
; if for every environment which assigns values to all the variables
; in either expression, they have the same value in that environment.

; One possibility might be to use satisfiable? to help implement equivalent?

; These procedures will be tested on expressions with few enough
; variables that generating truth tables will be a feasible approach.

; Examples:
;>  (satisfiable? 0)
;#f
;> (satisfiable? 1)
;#t
;>  (satisfiable? (band 'x (band 'y 'z)))
;#t
;> (satisfiable? (band 'x (band 'y (bnot 'y))))
;#f
;>  (satisfiable? (band (bor 'x (bnot 'y)) 0))
;#f
;>  (equivalent? 0 (band 'a (bnot 'a)))
;#t
;>  (equivalent? 0 'a) 
;#f
;>  (equivalent? (bor 'x (bor 'y 'z)) (bor 0 (bor 'z (bor 'x 'y))))
;#t
;> (equivalent? (bor 'x (band 'y 'z)) (band (bor 'x 'y) (bor 'x 'z)))
;#t
;> 
; ****************************************************************

(define (satisfiable? exp)
  (satisfy (tt-rows (truth-table exp))))
(define (satisfy ttable)
  (if (empty? ttable)
      #f
      ;checks if any of the values of the entries is 1, then it returns true
      (if (equal? (entry-value (car ttable)) 1)
          #t
          (satisfy (cdr ttable)))))

(define (equivalent? exp1 exp2)
  (if (and (not (satisfiable? exp1))(not (satisfiable? exp2)))
      #t
      (cond
        [(equal? (length (tt-rows (truth-table exp1)))(length (tt-rows (truth-table exp2))))
         ;if the truth tables are the same size check this following methods
         (equiv (tt-rows (truth-table exp1))(tt-rows (truth-table exp2)))]
        ;if either truth table just has 1 value (either 1 or 0) it checks the other tt whether all its values evaluate to either 1 or 0
        [(equal? 1 (length (tt-rows (truth-table exp1))))
         (equiv1 (entry-value (car (tt-rows (truth-table exp1)))) (tt-rows (truth-table exp2)))]
        [(equal? 1 (length (tt-rows (truth-table exp2))))
         (equiv1 (entry-value (car (tt-rows (truth-table exp2)))) (tt-rows (truth-table exp1)))]
        [else #f])))
(define (equiv tt1 tt2)
  ;if every line of the truth table matches the 2nd truth table
  (cond
    [(and (empty? tt1) (empty? tt2)) #t]
    [(equal? (entry-value (car tt1)) (entry-value (car tt2))) (equiv (cdr tt1) (cdr tt2))]
    [else #f]))
(define (equiv1 val tt1)
  (if (empty? tt1)
      #t
      (if (equal? val (entry-value (car tt1)))
          (equiv1 val (cdr tt1))
          #f)))


; ****************************************************************
; ** problem 8 ** (10 points)
; Write a procedure

; (find-exp tt)

; This procedure takes a truth table
; and returns a Boolean expression 
; for the given truth table.

; You may choose to use the sum-of-products algorithm
; from lecture, or some other method.
; Please include comments explaining your method
; in either case.

;Examples
;>  (boolean-exp? (find-exp tt-and))
;#t
;>  (equivalent? (find-exp tt-and) (band 'x 'y))
;#t
;>  (equivalent? (find-exp tt-imp) (bor (bnot 'a) 'b)) 
;#t
;>  (equivalent? (find-exp tt-xor) (bor (band 'u (bnot 'v)) (band (bnot 'u) 'v)))
;#t
;>  (boolean-exp? (find-exp tt-f1))
;#t
;> 
; ****************************************************************

(define (find-exp tt)
  (if (and (equal? (length (tt-rows tt)) 1) (number? (entry-value (car (tt-rows tt)))))
      (entry-value (car (tt-rows tt)))
      ;calls the findexp procedure
      (findexp (tt-vars tt) (tt-rows tt))))
(define (findexp vars rows)
  (cond
    ;two simple test cases
    [(empty? rows) 0]
    [(equal? (entry-value (car rows)) 1)
     ;calls sumBool if it yields a value of 1 (doing sum of products algorithm)
     (bor (sumBool vars (entry-key (car rows))) (findexp vars (cdr rows)))]
    [else (findexp vars (cdr rows))]))
(define (sumBool vars row)
  ;generates an expression for an individual satisfiable line for an expression
  (cond
    [(< (length vars) 2)
     (if (zero? (car row))
         (bnot (car vars))
         (car vars))]
    [(equal? (length vars) 2)
     (band (if (zero? (car row)) (bnot (car vars))(car vars))
           (if (zero? (last row)) (bnot (last vars)) (last vars)))]
    [else (band (if (zero? (car row))(bnot (car vars))(car vars))
                 (sumBool (cdr vars) (cdr row)))]
    ))
(require racket/trace)
;(trace sumBool)
;(trace findexp)
;(trace sumBool) 
     
; ****************************************************************
; ** problem 9 ** (10 points)
; Write a procedure

; (substitute-in exp sub-table)

; that takes a Boolean expression exp and a table sub-table each of whose
; entries has a key that is a variable and a value that is a
; Boolean expression, and returns the Boolean expression obtained
; by replacing every occurrence in exp of a variable in the sub-table with
; the corresponding Boolean expression.

; Hint: type-of and deep recursion on the structure of Boolean expressions.

; Examples
;> (substitute-in 0 (list (entry 'x 1)))
;0
;> (substitute-in 'x (list (entry 'x 1)))
;1
;> (substitute-in (band 'x 'y) (list (entry 'x (bnot 'z)) (entry 'y 0)))
;(band (bnot 'z) 0)
;> (substitute-in (band (bor 'x 'y) (bor (bnot 'x) 'y)) (list (entry 'x (bnot 1))))
;(band (bor (bnot 1) 'y) (bor (bnot (bnot 1)) 'y))
;> 
; ****************************************************************

(define (substitute-in exp sub-table)
  (cond
    [(equal? (type-of exp) 'constant) exp]
    [(equal? (type-of exp) 'variable) (find-exp (tt (list exp) sub-table))]
    ;sub is called if the above two dont happen
    [else (sub exp (all-vars exp) sub-table)]
    ))
(define (sub exp vars sub-table)
  (cond
    [(equal? (type-of exp) 'constant) exp]
    ;calls foundkey if it finds a variable within the boolean expression to substitute in
    [(equal? (type-of exp) 'variable) (foundKey exp sub-table)]
    ;if it finds a bexp within the recursion of the struct, it calls the helper on each argument until it finds a variable
    [(equal? (type-of exp) 'and) (band (sub (band-arg1 exp) vars sub-table)(sub (band-arg2 exp) vars sub-table))]
    [(equal? (type-of exp) 'or) (bor (sub (bor-arg1 exp) vars sub-table)(sub (bor-arg2 exp) vars sub-table))]
    [(equal? (type-of exp) 'not) (bnot (sub (bnot-arg exp) vars sub-table))]
    [else 'unspecified-variable]))
(define (foundKey var table)
  (cond
    [(empty? table) var]
    ;if there is something to match it to, return the value of that row in the table
    [(equal? (entry-key (car table)) var) (entry-value (car table))]
    [else (foundKey var (cdr table))]))

; ****************************************************************
; ** problem 10 ** (10 points)
; Write a procedure

; (match exp pat)

; that takes two Boolean expressions exp and pat and
; attempts to "match" the expression exp to the pattern pat.
; That is, it tries to find a table sub-table (as in the preceding
; problem) such that (substitute-in pat sub-table) returns
; the expression exp.  If this is not possible, it should return #f.

; Examples
;> (match 1 1)
;'()
;> (match 0 'x)
;(list (entry 'x 0))
;> (match 'z 0)
;#f
;>  (match 'z 'x)
;(list (entry 'x 'z))
;> (match (band 'y 'x) 'x)
;(list (entry 'x (band 'y 'x)))
;>  (match (bnot (band 'a 'b)) (bnot 'z))
;(list (entry 'z (band 'a 'b)))
;> (match (bor (band 'x 'y) 0) (bor 'a 0))
;(list (entry 'a (band 'x 'y)))
;> (match (band (bor (bnot 'z) 0) (bor (bnot 'z) 'y)) (band (bor 'a 'b) (bor 'a 'c)))
;(list (entry 'a (bnot 'z)) (entry 'b 0) (entry 'c 'y))
;> (match (band (band 'x 'y) 'z) (band (bor 'a 'b) 'c))   
;#f
;> (match (band 'x 'y) (band 'a 'a))
;#f
;> (substitute-in (band 'a 'a) (match (band (bor 0 1) (bor 0 1)) (band 'a 'a)))
;(band (bor 0 1) (bor 0 1))
;> 
; ****************************************************************

(define (match exp pat)
  (cond
    [(equal? exp pat) '()]
    [(and (number? exp)(symbol? pat)) (list (entry pat exp))]
    [(number? exp) (map (lambda (x)(entry x exp)) (all-vars pat))]
    [(number? pat) #f]
    ;if it finds a false in the list of entries generated by the helper (see below to see how that works), then return false
    ;if all the keys are not unique, the match is not possible, return false
    ;else, remove duplicates in which the key and value are the same, and return the final list
    [else (if (or (memq "false" (matchhelper exp pat '()))(not (unique-keys? (matchhelper exp pat '()))))
              #f
              (remove-duplicates (matchhelper exp pat '())))]))

(define (matchhelper exp pat lst)
  (cond
    ;check if pattern and exp match, if yes, appends a list of the two arguments of each exp and pat passing through the helper together
    ;if pat is a symbol, generate an entry with pat as the key and exp as the value
    ;in this case, exp could be an integer or a symbol or a boolean expression
    ;if a match is impossible, cons a false to the list - this is used above
    [(and(bor? pat)(bor? exp))
     (append (matchhelper (bor-arg1 exp)(bor-arg1 pat) lst)(matchhelper (bor-arg2 exp)(bor-arg2 pat) lst))]
    [(and(band? pat)(band? exp))
     (append (matchhelper (band-arg1 exp)(band-arg1 pat) lst)(matchhelper (band-arg2 exp)(band-arg2 pat) lst))]
    [(and (bnot? pat) (bnot? exp))
     (append (matchhelper (bnot-arg exp)(bnot-arg pat) lst))]
    [(symbol? pat) (cons (entry pat exp) lst)]
    [(number? pat) (append '() lst)]
    [else (cons "false" lst)]
    ))
        ;(trace matchhelper)          
; ********************************************************
; ********  testing, testing. 1, 2, 3 ....
; ********************************************************

(define *testing-flag* #t)
(define error display)  ;; turn off error messages

(define (test name got expected)
  (cond (*testing-flag*
	 (let* ((expected (if (procedure? expected)
			      (and (expected got) 'OK-TEST)
			      expected))
		(prefix (if (equal? got expected)
			    'OK
			    'X)))
	   (list 'testing name prefix 'got: got 'expected: expected)))))
	
(test 'hours hours (lambda (x) (> x 0)))


(test 'lookup  (lookup "first" test1) 1)
(test 'lookup  (lookup "third" test1) #f)
(test 'lookup  (lookup 'z test2) 1)
(test 'unique-keys?  (unique-keys? test1) #t)
(test 'unique-keys?  (unique-keys? test2) #f)


(test 'boolean-exp?  (boolean-exp? 0) #t)
(test 'boolean-exp?  (boolean-exp? 2) #f)
(test 'boolean-exp?  (boolean-exp? exp0) #t)
(test 'boolean-exp?  (boolean-exp? (band "hi" 'c)) #f)
(test 'boolean-exp?  (boolean-exp? (band 'x (bor 0 (bnot 1)))) #t)
(test 'boolean-exp?  (boolean-exp? (band 'x (bor 0 (bnot #t)))) #f)
(test 'type-of  (type-of 0) 'constant)
(test 'type-of  (type-of 'hi) 'variable)
(test 'type-of  (type-of (bnot (band 'x 0))) 'not)
(test 'type-of  (type-of (bor (band 'x 'y) (band 'x 'z))) 'or)
(test 'type-of  (type-of (band (bor 0 1) (bnot 'x))) 'and)

(test 'all-vars (all-vars 0) '())
(test 'all-vars (all-vars (bnot (band 'x (band 'y (bor 'x 'z))))) '(x y z))
(test 'all-vars (all-vars (band 1 (bor 0 (bnot 'u)))) '(u))
(test 'all-vars (all-vars (band (band 'x 'y) (band 'y 'x))) '(x y))
(test 'all-vars (all-vars (bor (bor (bor 'c 'b) (bor 'a 'b)) 'c)) '(c b a))


(test 'eval-in-env (eval-in-env 1 environ1) 1)
(test 'eval-in-env (eval-in-env (bor 0 0) '()) 0)
(test 'eval-in-env (eval-in-env 'x environ1) 0)
(test 'eval-in-env (eval-in-env 'x environ2) 1)
(test 'eval-in-env (eval-in-env (bnot 'z) environ1) 1)
(test 'eval-in-env (eval-in-env (bor 'y (bnot 'x)) environ2) 0)
(test 'eval-in-env (eval-in-env (band (band (bor 'u 'x) (bor 'w 0)) (bnot (band 'y 'z))) environ2) 1)
(test 'eval-in-env (eval-in-env exp5 environ1) 0)
(test 'eval-in-env (eval-in-env (band 'y (bor 'x 'u)) (list (entry 'x 0) (entry 'y 1))) 'unspecified-variable)


(test 'all-combs (all-combs 0) '(()))
(test 'all-combs (all-combs 1) '((0) (1)))
(test 'all-combs (all-combs 2) '((0 0) (0 1) (1 0) (1 1)))
(test 'all-combs (all-combs 3) '((0 0 0) (0 0 1) (0 1 0) (0 1 1) (1 0 0) (1 0 1) (1 1 0) (1 1 1)))


(test 'truth-table (truth-table exp0) (tt '() (list (entry '() 1))))
(test 'truth-table (truth-table exp1) 
      (tt '(x y)
	  (list (entry '(0 0) 0) (entry '(0 1) 1) (entry '(1 0) 1) (entry '(1 1) 1))))
(test 'truth-table (truth-table exp5) (tt
				       '(x y z)
				       (list
					(entry '(0 0 0) 1)
					(entry '(0 0 1) 1)
					(entry '(0 1 0) 0)
					(entry '(0 1 1) 0)
					(entry '(1 0 0) 1)
					(entry '(1 0 1) 1)
					(entry '(1 1 0) 1)
					(entry '(1 1 1) 1))))



(test satisfiable?  (satisfiable? 0) #f)
(test satisfiable? (satisfiable? 1) #t)
(test satisfiable?  (satisfiable? (band 'x (band 'y 'z))) #t)
(test satisfiable? (satisfiable? (band 'x (band 'y (bnot 'y)))) #f)
(test satisfiable?  (satisfiable? (band (bor 'x (bnot 'y)) 0)) #f)
(test equivalent?  (equivalent? 0 (band 'a (bnot 'a))) #t)
(test equivalent?  (equivalent? 0 'a) #f)
(test equivalent?  (equivalent? (bor 'x (bor 'y 'z)) (bor 0 (bor 'z (bor 'x 'y)))) #t)
(test equivalent? (equivalent? (bor 'x (band 'y 'z)) (band (bor 'x 'y) (bor 'x 'z))) #t)


(test 'find-exp  (boolean-exp? (find-exp tt-and)) #t)
(test 'find-exp  (equivalent? (find-exp tt-and) (band 'x 'y)) #t)
(test 'find-exp  (equivalent? (find-exp tt-imp) (bor (bnot 'a) 'b)) #t)
(test 'find-exp  (equivalent? (find-exp tt-xor) (bor (band 'u (bnot 'v)) (band (bnot 'u) 'v))) #t)
(test 'find-exp  (boolean-exp? (find-exp tt-f1)) #t)

(test 'substitute-in (substitute-in 0 (list (entry 'x 1))) 0)
(test 'substitute-in (substitute-in 'x (list (entry 'x 1))) 1)
(test 'substitute-in (substitute-in (band 'x 'y) (list (entry 'x (bnot 'z)) (entry 'y 0))) (band (bnot 'z) 0))
(test 'substitute-in (substitute-in (band (bor 'x 'y) (bor (bnot 'x) 'y)) (list (entry 'x (bnot 1)))) (band (bor (bnot 1) 'y) (bor (bnot (bnot 1)) 'y)))


(test 'match (match 1 1) '())
(test 'match (match 0 'x) (list (entry 'x 0)))
(test 'match (match 'z 0) #f)
(test 'match  (match 'z 'x) (list (entry 'x 'z)))
(test 'match (match (band 'y 'x) 'x) (list (entry 'x (band 'y 'x))))
(test 'match  (match (bnot (band 'a 'b)) (bnot 'z)) (list (entry 'z (band 'a 'b))))
(test 'match (match (bor (band 'x 'y) 0) (bor 'a 0)) (list (entry 'a (band 'x 'y))))
(test 'match (match (band (bor (bnot 'z) 0) (bor (bnot 'z) 'y)) (band (bor 'a 'b) (bor 'a 'c))) (list (entry 'a (bnot 'z)) (entry 'b 0) (entry 'c 'y)))
(test 'match (match (band (band 'x 'y) 'z) (band (bor 'a 'b) 'c)) #f)
(test 'match (match (band 'x 'y) (band 'a 'a)) #f)
(test 'match (substitute-in (band 'a 'a) (match (band (bor 0 1) (bor 0 1)) (band 'a 'a))) (band (bor 0 1) (bor 0 1)))



; **************** end of hw #4 *********************************