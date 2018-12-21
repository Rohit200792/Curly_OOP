#lang plait
#|Author Rohit Singh|#
(require "class.rkt"
         "inherit.rkt")

(define-type ClassT
  (classT [super-name : Symbol]
          [fields : (Listof (Symbol * Type))]
          [methods : (Listof (Symbol * MethodT))]))

(define-type MethodT
  (methodT [arg-type : Type]
           [result-type : Type]
           [body-expr : ExpI]))

(define-type Type
  (numT)
  (nullT)                                              ;;Type variant for null Part4
  (objT [class-name : Symbol]))

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))


(define (get-all-field-types class-name t-classes)
  (if (equal? class-name 'Object)
      empty        
      (type-case ClassT (find t-classes class-name)
        [(classT super-name fields methods)
         (append 
          (get-all-field-types super-name t-classes)
          (map snd fields))])))

;; ----------------------------------------

(define (make-find-in-tree class-items)
  (lambda (name class-name t-classes)
    (local [(define t-class (find t-classes class-name))
            (define items (class-items t-class))
            (define super-name 
              (classT-super-name t-class))]
      (if (equal? super-name 'Object)
          (find items name)
          (try (find items name)
               (lambda ()
                 ((make-find-in-tree class-items)
                  name 
                  super-name
                  t-classes)))))))

(define find-field-in-tree
  (make-find-in-tree classT-fields))

(define find-method-in-tree
  (make-find-in-tree classT-methods))

;; ----------------------------------------

(define (is-subclass? name1 name2 t-classes)
  (cond
    [(equal? name1 name2) #t]
    [(equal? name1 'Object) #f]
    [else
     (type-case ClassT (find t-classes name1)
       [(classT super-name fields methods)
        (is-subclass? super-name name2 t-classes)])]))

(define (is-subtype? t1 t2 t-classes)
  (type-case Type t2
    [(objT name2)
     (type-case Type t1 
       [(objT name1)
        (is-subclass? name1 name2 t-classes)]
       [(nullT) #t]                                                             ;;class subtype as null type Part4
       [else #f])]
    [else (equal? t1 t2)]))

(module+ test
  (define a-t-class (values 'A (classT 'Object empty empty)))
  (define b-t-class (values 'B (classT 'A empty empty)))

  (test (is-subclass? 'Object 'Object empty)
        #t)
  (test (is-subclass? 'A 'B (list a-t-class b-t-class))
        #f)
  (test (is-subclass? 'B 'A (list a-t-class b-t-class))
        #t)

  (test (is-subtype? (numT) (numT) empty)
        #t)
  (test (is-subtype? (numT) (objT 'Object) empty)
        #f)
  (test (is-subtype? (objT 'Object) (numT) empty)
        #f)
  (test (is-subtype? (objT 'A) (objT 'B) (list a-t-class b-t-class))
        #f)
  (test (is-subtype? (objT 'B) (objT 'A) (list a-t-class b-t-class))
        #t))

;; ----------------------------------------

(define typecheck-expr : (ExpI (Listof (Symbol * ClassT)) Type Type Number -> Type)
  (lambda (expr t-classes this-type arg-type exp-mode)
    (local [(define (recur expr)
              (typecheck-expr expr t-classes this-type arg-type exp-mode))
            (define (typecheck-nums l r)
              (type-case Type (recur l)
                [(numT)
                 (type-case Type (recur r)
                   [(numT) (numT)]
                   [else (type-error r "num")])]
                [else (type-error l "num")]))]
      (type-case ExpI expr
        [(numI n) (numT)]
        [(plusI l r) (typecheck-nums l r)]
        [(multI l r) (typecheck-nums l r)]
        [(castI l r) (local [(define cast-obj (recur r))]                                 ;;case for type-checking castI Part2
                       (type-case Type cast-obj
                         ((objT s)
                          (cond
                            [(is-subtype? (objT l) cast-obj t-classes) (objT l)]
                            [(is-subtype? cast-obj (objT l) t-classes) (objT l)]
                            [else (type-error expr "not a subclass/superclass")]))
                         (else (type-error expr "not an object"))))]
        [(if0I chk thn els) (type-case Type (recur chk)                                  ;;case for type-checking if0I Part3
                              [(numT)(lr-type expr (recur thn)
                                                         (recur els) t-classes)]
                              [else (type-error expr "check is not a number")])]
        [(nullI) (nullT)]                                                                ;;case for type-checking nullI Part4
        [(argI) (if (eq? exp-mode 1)
                     arg-type
                     (type-error expr "arg not allowed in main expression"))]            ;;error for arg in main expression Part1
        [(thisI) (if (eq? exp-mode 1)
                     this-type
                     (type-error expr "this not allowed in main expression"))]           ;;error for this in main expression Part1
        [(newI class-name exprs)
         (local [(define arg-types (map recur exprs))
                 (define field-types
                   (get-all-field-types class-name t-classes))]
           (if (and (= (length arg-types) (length field-types))
                    (foldl (lambda (b r) (and r b))
                           #t
                           (map2 (lambda (t1 t2) 
                                   (is-subtype? t1 t2 t-classes))
                                 arg-types
                                 field-types)))
               (objT class-name)
               (type-error expr "field type mismatch")))]
        [(getI obj-expr field-name)
         (type-case Type (recur obj-expr)
           [(objT class-name)
            (find-field-in-tree field-name
                                class-name
                                t-classes)]
           [else (type-error obj-expr "object")])]
        [(setI obj-expr field-name field-exp)                                             ;;case for type-checking setI Part5
         (local [(define obj-type (recur obj-expr))
                 (define new-field-type (recur field-exp))]
            (type-case Type obj-type
           [(objT class-name)
            (local [(define arg-field-type (find-field-in-tree field-name
                                                               class-name
                                                               t-classes))]
              (if (is-subtype? new-field-type arg-field-type t-classes)
                   new-field-type
                  (type-error obj-expr "field types dont match")))]
           [else (type-error obj-expr "object")]))]
        [(sendI obj-expr method-name arg-expr)
         (local [(define obj-type (recur obj-expr))
                 (define arg-type (recur arg-expr))]
           (type-case Type obj-type
             [(objT class-name)
              (typecheck-send class-name method-name
                              arg-expr arg-type
                              t-classes)]
             [else
              (type-error obj-expr "object")]))]
        [(superI method-name arg-expr)
         (local [(define arg-type (recur arg-expr))
                 (define this-class
                   (find t-classes (objT-class-name this-type)))]
           (typecheck-send (classT-super-name this-class)
                           method-name
                           arg-expr arg-type
                           t-classes))]))))
;; typecheck-expr-method----------------------------------------
(define typecheck-expr-method : (ExpI (Listof (Symbol * ClassT)) Type Type -> Type)  ;;intermediate function to set up tecpecheck-expr for class methods Part1
  (lambda (expr t-classes this-type arg-type)
        (typecheck-expr expr t-classes this-type arg-type 1)))
;; lr-type----------------------------------------
(define (lr-type [expr : ExpI] [type1 : Type] [type2 : Type] [list_classes : (Listof (Symbol * ClassT))]) : Type
  (type-case Type type1                                                             ;;helper function to check type for if0 then and else Part3
    [(numT)(type-case Type type2
               [(numT) (numT)]
               [else (type-error expr "then else type mismatch")])]
    [(objT n1) (type-case Type type2
                [(objT n2)
                 (if (equal? n1 n2)
                     type1
                     (local [(define class1_def (find list_classes n1))]
                       (find-joint-subtype (classT-super-name class1_def) (objT-class-name type2)
                                           (classT-super-name class1_def) list_classes)))]
                 [(nullT) type1]
                 [else (type-error expr "then else type mismatch")])]
   [(nullT) (type-case Type type2
                [(objT n2) type2]
                 [(nullT) (nullT)]
                 [else (type-error expr "then else type mismatch")])]))

(define (find-joint-subtype [class1 : Symbol] [class2 : Symbol] [class_mem : Symbol] [list_classes : (Listof (Symbol * ClassT))]) : Type
  (cond
    [(equal? class1 class2) (objT class1)]
    [(and (equal? class1 'Object) (equal? class2 class_mem)) (objT 'Object)]
    [(equal? class1 'Object) (local [(define class2_def (find list_classes class2))]
                               (find-joint-subtype (classT-super-name class2_def) class_mem
                                                   class_mem list_classes))]
    [else (local [(define class1_def (find list_classes class1))]
                       (find-joint-subtype (classT-super-name class1_def) class2
                                           class_mem list_classes))]))
;; ----------------------------------------
(define (typecheck-send [class-name : Symbol]
                        [method-name : Symbol]
                        [arg-expr : ExpI]
                        [arg-type : Type]
                        [t-classes : (Listof (Symbol * ClassT))])
  (type-case MethodT (find-method-in-tree
                      method-name
                      class-name
                      t-classes)
    [(methodT arg-type-m result-type body-expr)
     (if (is-subtype? arg-type arg-type-m t-classes)
         result-type
         (type-error arg-expr (to-string arg-type-m)))]))

(define (typecheck-method [method : MethodT]
                          [this-type : Type]
                          [t-classes : (Listof (Symbol * ClassT))]) : ()
  (type-case MethodT method
    [(methodT arg-type result-type body-expr)
     (if (is-subtype? (typecheck-expr-method body-expr t-classes
                                      this-type arg-type)
                      result-type
                      t-classes)
         (values)
         (type-error body-expr (to-string result-type)))]))

(define (check-override [method-name : Symbol]
                        [method : MethodT]
                        [this-class : ClassT]
                        [t-classes : (Listof (Symbol * ClassT))])
  (local [(define super-name 
            (classT-super-name this-class))
          (define super-method
            (try
             ;; Look for method in superclass:
             (find-method-in-tree method-name
                                  super-name
                                  t-classes)
             ;; no such method in superclass:
             (lambda () method)))]
    (if (and (equal? (methodT-arg-type method)
                     (methodT-arg-type super-method))
             (equal? (methodT-result-type method)
                     (methodT-result-type super-method)))
        (values)
        (error 'typecheck (string-append
                           "bad override of "
                           (to-string method-name))))))

(define (typecheck-class [class-name : Symbol]
                         [t-class : ClassT]
                         [t-classes : (Listof (Symbol * ClassT))])
  (type-case ClassT t-class
    [(classT super-name fields methods)
     (map (lambda (m)
            (begin
              (typecheck-method (snd m) (objT class-name) t-classes)
              (check-override (fst m) (snd m) t-class t-classes)))
          methods)]))

(define (typecheck [a : ExpI]
                   [t-classes : (Listof (Symbol * ClassT))]) : Type
  (begin
    (map (lambda (tc)
           (typecheck-class (fst tc) (snd tc) t-classes))
         t-classes)
    (typecheck-expr a t-classes (objT 'Object) (numT) 0))) 

;; ----------------------------------------

(module+ test
  (define posn-t-class
    (values 'Posn
            (classT 'Object
                    (list (values 'x (numT)) (values 'y (numT)))
                    (list (values 'mdist
                                  (methodT (numT) (numT) 
                                           (plusI (getI (thisI) 'x) (getI (thisI) 'y))))
                          (values 'addDist
                                  (methodT (objT 'Posn) (numT)
                                           (plusI (sendI (thisI) 'mdist (numI 0))
                                                  (sendI (argI) 'mdist (numI 0)))))))))

  (define posn3D-t-class 
    (values 'Posn3D
            (classT 'Posn
                    (list (values 'z (numT)))
                    (list (values 'mdist
                                  (methodT (numT) (numT)
                                           (plusI (getI (thisI) 'z) 
                                                  (superI 'mdist (argI)))))))))
  (define length-t-class
    (values 'Length
            (classT 'Object
                    (list (values 'len (numT)))
                    (list))))
                    

  (define square-t-class 
    (values 'Square
            (classT 'Object
                    (list (values 'topleft (objT 'Posn)))
                    (list (values 'area
                                  (methodT (numT) (numT)
                                           (multI (argI) (argI))))
                          (values 'areaObj
                                  (methodT (objT 'Length) (numT)
                                           (multI (getI (argI) 'len)
                                                  (getI (argI) 'len))))
                          (values 'perimeter
                                  (methodT (numT) (numT)
                                           (plusI (plusI (argI) (argI))
                                                  (plusI (argI) (argI)))))))))

  (define (typecheck-posn a)
    (typecheck a
               (list posn-t-class posn3D-t-class length-t-class square-t-class)))

;;Object Declarations ----------------------------------------  
  (define new-posn27 (newI 'Posn (list (numI 2) (numI 7))))
  (define new-posn94 (newI 'Posn (list (numI 9) (numI 4))))  
  (define new-posn531 (newI 'Posn3D (list (numI 5) (numI 3) (numI 1))))
  (define new-square27 (newI 'Square (list new-posn27)))  
  (define new-square94 (newI 'Square (list new-posn94)))
;; ----------------------------------------
  (test (typecheck-posn (sendI new-posn27 'mdist (numI 0)))
        (numT))
  (test (typecheck-posn (sendI new-posn531 'mdist (numI 0)))
        (numT))  
  (test (typecheck-posn (sendI new-posn531 'addDist new-posn27))
        (numT))  
  (test (typecheck-posn (sendI new-posn27 'addDist new-posn531))
        (numT))

  (test (typecheck-posn (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1))))))
        (objT 'Square))
  (test (typecheck-posn (newI 'Square (list (newI 'Posn3D (list (numI 0) (numI 1) (numI 3))))))
        (objT 'Square))
  
  (test (typecheck (multI (numI 1) (numI 2))
                   empty)
        (numT))

  (test/exn (typecheck-posn (sendI (numI 10) 'mdist (numI 0)))
            "no type")
  (test/exn (typecheck-posn (sendI new-posn27 'mdist new-posn27))
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object empty))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (newI 'Object empty) (numI 1))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object (list (numI 1))))
                       empty)
            "no type")
  (test/exn (typecheck (getI (numI 1) 'x)
                       empty)
            "no type")
  (test/exn (typecheck (numI 10)
                       (list posn-t-class
                             (values 'Other
                                     (classT 'Posn
                                             (list)
                                             (list (values 'mdist
                                                           (methodT (objT 'Object) (numT) 
                                                                    (numI 10))))))))
            "bad override")
  (test/exn (typecheck-method (methodT (numT) (objT 'Object) (numI 0)) (objT 'Object) empty)
            "no type")
  (test/exn (typecheck (numI 0)
                       (list square-t-class
                             (values 'Cube
                                     (classT 'Square
                                             empty
                                             (list
                                              (values 'm
                                                      (methodT (numT) (numT)
                                                               ;; No such method in superclass:
                                                               (superI 'm (numI 0)))))))))
            "not found")
;; Test Case Part1----------------------------------------

  (test (typecheck new-posn27
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Posn))
  
    (test/exn (typecheck (argI)
                       (list posn-t-class
                             (values 'Other
                                     (classT 'Posn
                                             (list)
                                             (list (values 'mdist
                                                           (methodT (numT) (numT)
                                                                    (numI 10))))))))
            "arg not allowed in main expression")
    (test/exn (typecheck (thisI)
                       (list posn-t-class
                             (values 'Other
                                     (classT 'Posn
                                             (list)
                                             (list (values 'mdist
                                                           (methodT (numT) (numT)
                                                                    (numI 10))))))))
            "this not allowed in main expression")
;; Test Case Part2----------------------------------------
  (test (typecheck (castI 'Posn3D new-posn27) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Posn3D))
  (test (typecheck (castI 'Posn new-posn531) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Posn))
  (test/exn (typecheck (castI 'Square (numI 4))
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           "not an object")
  (test/exn (typecheck (castI 'Square new-posn531) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           "not a subclass/superclass")
;; Test Case Part3----------------------------------------
  (test (typecheck (if0I (numI 1) (numI 2) (numI 3)) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (numT))  
  (test (typecheck (if0I (numI 1) new-posn27 new-posn94) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Posn))
  (test (typecheck (if0I (numI 1) new-posn531 new-posn94) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Posn))
  (test (typecheck (if0I (numI 1) new-posn531 new-square94) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Object))
  (test (typecheck (if0I (numI 1) new-posn531 (nullI)) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Posn3D))
  (test (typecheck (if0I (numI 1) (nullI) new-posn531) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (objT 'Posn3D))
  (test (typecheck (if0I (numI 1) (nullI) (nullI)) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           (nullT))  
  (test/exn (typecheck (if0I new-posn27 (numI 2) (numI 3)) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           "check is not a number") 
  (test/exn (typecheck (if0I (numI 0) (numI 2) new-posn27) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           "then else type mismatch")
  (test/exn (typecheck (if0I (numI 0) new-posn27 (numI 3)) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           "then else type mismatch")
  (test/exn (typecheck (if0I (numI 1) (numI 1) (nullI)) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           "then else type mismatch")
  (test/exn (typecheck (if0I (numI 1) (nullI) (numI 1)) 
                       (list posn-t-class posn3D-t-class length-t-class square-t-class))
           "then else type mismatch")    
;; Test Case Part4----------------------------------------
  
  (test (is-subtype? (objT 'B) (objT 'A) (list a-t-class b-t-class))
        #t)
  (test (is-subtype? (nullT) (objT 'B) (list a-t-class b-t-class))
        #t)
  (test (is-subtype? (nullT) (objT 'A) (list a-t-class b-t-class))
        #t)
  (test (is-subtype? (objT 'A) (nullT) (list a-t-class b-t-class))
        #f)
  (test (is-subtype? (numT) (nullT) (list a-t-class b-t-class))
        #f)
  (test (is-subtype? (nullT) (numT) (list a-t-class b-t-class))
        #f)
  
  (test (typecheck-send 'Square 'areaObj (nullI) (nullT)
                        (list posn-t-class posn3D-t-class length-t-class square-t-class))
        (numT))
  (test (typecheck-send 'Square 'perimeter (numI 4) (numT)
                        (list posn-t-class posn3D-t-class length-t-class square-t-class))
        (numT))
  (test/exn (typecheck-send 'Square 'perimeter (nullI) (nullT)
                        (list posn-t-class posn3D-t-class length-t-class square-t-class))
        "no type")  

   (test (typecheck (newI 'Square (list (nullI)))
                   (list posn-t-class posn3D-t-class length-t-class square-t-class))
            (objT 'Square))
  (test/exn (typecheck (getI (nullI) 'x)
                   (list posn-t-class posn3D-t-class length-t-class square-t-class))
            "not object")
  (test/exn (typecheck (getI (nullI) 'x)
                   (list posn-t-class posn3D-t-class length-t-class square-t-class))
            "not object")
  (test/exn (typecheck (sendI (nullI) 'length (numI 5))
                   (list posn-t-class posn3D-t-class length-t-class square-t-class))
            "not object")  
;; Test Case Part5----------------------------------------
 (test (typecheck (setI new-posn27 'x (numI 5))
             (list posn-t-class posn3D-t-class length-t-class square-t-class))
       (numT))

 (test (typecheck (setI new-square27 'topleft new-posn94)
             (list posn-t-class posn3D-t-class length-t-class square-t-class))
       (objT 'Posn))
 (test/exn (typecheck (setI new-square27 'topleft (numI 5))
             (list posn-t-class posn3D-t-class length-t-class square-t-class))
       "field types dont match")
 (test/exn (typecheck (setI new-posn27 'x new-square94)
             (list posn-t-class posn3D-t-class length-t-class square-t-class))
       "field types dont match")
 (test/exn (typecheck (setI new-posn27 'x new-posn531)
             (list posn-t-class posn3D-t-class length-t-class square-t-class))
       "field types dont match")
 (test/exn (typecheck (setI (numI 5) 'x (numI 6))
             (list posn-t-class posn3D-t-class length-t-class square-t-class))
       "not object"))

;; ----------------------------------------

(define strip-types : (ClassT -> ClassI)
  (lambda (t-class)
    (type-case ClassT t-class
      [(classT super-name fields methods)
       (classI
        super-name
        (map fst fields)
        (map (lambda (m)
               (values (fst m)
                       (type-case MethodT (snd m)
                         [(methodT arg-type result-type body-expr)
                          body-expr])))
             methods))])))
  
(define interp-t : (ExpI (Listof (Symbol * ClassT)) -> Value)
  (lambda (a t-classes)
    (interp-i a
              (map (lambda (c)
                     (values (fst c) (strip-types (snd c))))
                   t-classes))))

(module+ test
  (define (interp-t-posn a)
    (interp-t a
              (list posn-t-class posn3D-t-class)))
  
  (test (interp-t-posn (sendI new-posn27 'mdist (numI 0)))
        (numV 9))  
  (test (interp-t-posn (sendI new-posn531 'mdist (numI 0)))
        (numV 9))
  (test (interp-t-posn (sendI new-posn531 'addDist new-posn27))
        (numV 18))
  (test (interp-t-posn (sendI new-posn27 'addDist new-posn531))
        (numV 18)))

