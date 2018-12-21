#lang plait
#|Author Rohit Singh|#
(define-type Exp
  (numE [n : Number])
  (plusE [lhs : Exp]
         [rhs : Exp])
  (multE [lhs : Exp]
         [rhs : Exp])
  (castE [lhs : Symbol]                                ;;Exp variant for cast operator Part2
         [rhs : Exp])
  (if0E [chk : Exp]                                    ;;Exp variant for if0 operator Part3
       [thn : Exp]
       [els : Exp])
  (nullE)                                              ;;Exp variant for null expression Part4
  (argE)
  (thisE)
  (newE [class-name : Symbol]
        [args : (Listof Exp)])
  (getE [obj-expr : Exp]
        [field-name : Symbol])
  (setE [obj-expr : Exp]                              ;;Exp variant for set operator Part5
        [field-name : Symbol]
        [field-exp : Exp])
  (sendE [obj-expr : Exp]
         [method-name : Symbol]
         [arg-expr : Exp])
  (ssendE [obj-expr : Exp]
          [class-name : Symbol]
          [method-name : Symbol]
          [arg-expr : Exp]))

(define-type Class
  (classC [field-names : (Listof Symbol)]
          [super-name : Symbol]                      ;;added id for supername for is-subclass? Part2
          [methods : (Listof (Symbol * Exp))]))

(define-type Value
  (nullV)                                            ;;Value variant for null expressions Part4
  (numV [n : Number])
  (objV [class-name : Symbol]
        [super-name : Symbol]
        [field-values : (Listof (Boxof Value))]))    ;;field-values stores as box of values Part5

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (find [l : (Listof (Symbol * 'a))] [name : Symbol]) : 'a
  (type-case (Listof (Symbol * 'a)) l
    [empty
     (error 'find (string-append "not found: " (symbol->string name)))]
    [(cons p rst-l)
     (if (symbol=? (fst p) name)
         (snd p)
         (find rst-l name))]))

(module+ test
  (test (find (list (values 'a 1)) 'a)
        1)
  (test (find (list (values 'a 1) (values 'b 2)) 'b)
        2)
  (test/exn (find empty 'a)
            "not found: a")
  (test/exn (find (list (values 'a 1)) 'x)
            "not found: x"))

;; ----------------------------------------

(define interp : (Exp (Listof (Symbol * Class)) Value Value -> Value)
  (lambda (a classes this-val arg-val)
    (local [(define (recur expr)
              (interp expr classes this-val arg-val))]
      (type-case Exp a
        [(numE n) (numV n)]
        [(plusE l r) (num+ (recur l) (recur r))]
        [(multE l r) (num* (recur l) (recur r))] 
        [(castE l r) (local [(define result (recur r))]                            ;;case for interpreting castE Part2
                       (if (or (equal? (objV-class-name result) l)
                               (is-subclassE? (objV-super-name result) l classes))
                           result
                           (error 'interp "not a subclass")))]
        [(if0E chk thn els) (if (eq? 0 (numV-n (recur chk)))                       ;;case for interpreting if0E Part3
                                (recur thn)           
                                (recur els))]        
        [(thisE) this-val]
        [(argE) arg-val]
        [(nullE) (nullV)]                                                         ;;case for interpreting nullE Part4 
        [(newE class-name field-exprs)
         (local [(define c (find classes class-name))
                 (define vals (map recur field-exprs))
                 (define val-box (map box vals))]
           (if (= (length vals) (length (classC-field-names c)))
               (objV class-name (classC-super-name c) val-box)
               (error 'interp "wrong field count")))]
        [(getE obj-expr field-name)
         (type-case Value (recur obj-expr)
           [(objV class-name super-name field-vals)
            (type-case Class (find classes class-name)
              [(classC field-names super-name methods)
               (find (map2 (lambda (n v) (values n v))
                           field-names
                           (map unbox field-vals))
                     field-name)])]
           [else (error 'interp "not an object")])]
        [(setE obj-expr field-name field-expr)                                    ;;case for interpreting setE Part5
         (local [(define obj-val (recur obj-expr))]
         (type-case Value obj-val
           [(objV class-name super-name field-vals)
            (type-case Class (find classes class-name)
              [(classC field-names super-name methods)
               (begin
                 (set-box! (find (map2 (lambda (n v) (values n v))
                           field-names
                           field-vals)
                               field-name)
                           (recur field-expr))
                 obj-val)])]
           [else (error 'interp "not an object")]))]                          
        [(sendE obj-expr method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (type-case Value obj
             [(objV class-name suoer-name field-vals)
              (call-method class-name method-name classes
                           obj arg-val)]
             [else (error 'interp "not an object")]))]
        [(ssendE obj-expr class-name method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (call-method class-name method-name classes
                        obj arg-val))]))))

(define (call-method class-name method-name classes
                     obj arg-val)
  (type-case Class (find classes class-name)
    [(classC field-names super-name methods)
     (let ([body-expr (find methods method-name)])
       (interp body-expr
               classes
               obj
               arg-val))]))
;;is-sublassE? ----------------------------------------
(define (is-subclassE? (name1 : Symbol) (name2 : Symbol) (list_classes : (Listof (Symbol * Class)))) : Boolean   ;;helper function for intepreting castE Part2
    (cond
    [(equal? name1 name2) #t]
    [(equal? name1 'Object) #f] 
    [else
     (type-case Class (find list_classes name1)
       [(classC field-names super-name methods)
        (is-subclassE? super-name name2 list_classes)])]))
;;num-op ----------------------------------------
(define (num-op [op : (Number Number -> Number)]
                [op-name : Symbol] 
                [x : Value]
                [y : Value]) : Value
  (cond
    [(and (numV? x) (numV? y))
     (numV (op (numV-n x) (numV-n y)))]
    [else (error 'interp "not a number")]))

(define (num+ x y) (num-op + '+ x y))
(define (num* x y) (num-op * '* x y))

;; ----------------------------------------
;; Examples

(module+ test
  (define posn-class
    (values 'Posn
            (classC 
             (list 'x 'y)
             'Object
             (list (values 'mdist
                           (plusE (getE (thisE) 'x) (getE (thisE) 'y)))
                   (values 'addDist
                           (plusE (sendE (thisE) 'mdist (numE 0))
                                  (sendE (argE) 'mdist (numE 0))))
                   (values 'addX
                           (plusE (getE (thisE) 'x) (argE)))
                   (values 'multY (multE (argE) (getE (thisE) 'y)))
                   (values 'factory12 (newE 'Posn (list (numE 1) (numE 2))))))))
    
  (define posn3D-class
    (values 'Posn3D
            (classC 
             (list 'x 'y 'z)
             'Posn
             (list (values 'mdist (plusE (getE (thisE) 'z)
                                         (ssendE (thisE) 'Posn 'mdist (argE))))
                   (values 'addDist (ssendE (thisE) 'Posn 'addDist (argE)))))))
    (define length-class
    (values 'Length
            (classC
            (list 'length)
            'Object
            (list)))) 
            
  (define square-class  
    (values 'Square
            (classC
             (list 'topleft 'len)                                                                ;;topleft- object of Posn class, len is a number 
             'Object
             (list (values 'area (multE (getE (thisE) 'len)                                      ;;does not need an argument, uses class variable len (-> Number)
                                           (getE (thisE) 'len)))
                   (values 'areaObj (multE (getE (argE) 'length)                                 ;;takes Length object as argument (Object -> Number)
                                           (getE (argE) 'length)))
                   (values 'perimeter (plusE (plusE (argE) (argE))                               ;;takes number as argument (Number -> Number)
                                           (plusE (argE) (argE))))))))
  (define rectangle-class
    (values 'Rectangle
            (classC
             (list 'len 'wid)                                                                    ;;len and wid are objects of Length class 
             'Object
             (list (values 'area (multE (getE (getE (thisE) 'len) 'length)                       ;;does not need any argument, uses class variables len and wid (-> Number)
                                        (getE (getE (thisE) 'wid) 'length)))
                   (values 'make-len-bigger (setE (getE (thisE) 'len)                            ;;updates the class variable len (Number -> Number)
                                                  'length (argE)))
                   (values 'calc-bigger-area (sendE (thisE) 'area                                ;;calculates increased area with updated len (Number -> Number) (Imperative)
                                                    (sendE (thisE) 'make-len-bigger
                                                                         (argE)))))))) 
                   
 

  (define posn27 (newE 'Posn (list (numE 2) (numE 7))))
  (define posn531 (newE 'Posn3D (list (numE 5) (numE 3) (numE 1))))
  (define square27-5 (newE 'Square (list posn27 (numE 5))))
  (define rectangle5-10 (newE 'Rectangle (list (newE 'Length (list (numE 5))) (newE 'Length (list (numE 10))))))   

  (define (interp-posn a)
    (interp a (list posn-class posn3D-class length-class rectangle-class square-class) (numV -1) (numV -1))))

;; ----------------------------------------
(module+ test
  (test (interp (numE 10) 
                empty (objV 'Object 'Object empty) (numV 0))
        (numV 10))
  (test (interp (plusE (numE 10) (numE 17))
                empty (objV 'Object 'Object empty) (numV 0))
        (numV 27))
  (test (interp (multE (numE 10) (numE 7))
                empty (objV 'Object 'Object empty) (numV 0))
        (numV 70))

  (test (interp-posn (newE 'Posn (list (numE 2) (numE 7))))
        (objV 'Posn 'Object (list (box (numV 2)) (box (numV 7)))))

  (test (interp-posn (sendE posn27 'mdist (numE 0)))
        (numV 9))
  
  (test (interp-posn (sendE posn27 'addX (numE 10)))
        (numV 12))

  (test (interp-posn (sendE (ssendE posn27 'Posn 'factory12 (numE 0))
                            'multY
                            (numE 15)))
        (numV 30))

  (test (interp-posn (sendE posn531 'addDist posn27))
        (numV 18))
  
  (test/exn (interp-posn (plusE (numE 1) posn27))
            "not a number")
  (test/exn (interp-posn (getE (numE 1) 'x))
            "not an object")
  (test/exn (interp-posn (sendE (numE 1) 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (ssendE (numE 1) 'Posn 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (newE 'Posn (list (numE 0))))
            "wrong field count")
;;Test Part2 ----------------------------------------
(test (is-subclassE? 'Posn
                     'Object (list posn-class posn3D-class))
  #t)  
(test (is-subclassE? 'Posn
                     'Posn (list posn-class posn3D-class))
  #t)
(test (is-subclassE? 'Posn3D
                     'Posn (list posn-class posn3D-class))
  #t)
(test (is-subclassE? 'Posn
                     'Posn3D (list posn-class posn3D-class))
  #f)
  (test (interp (castE 'Posn posn531)
                (list posn-class posn3D-class)
                (objV 'Object 'Object empty) (numV 0))
        (objV 'Posn3D 'Posn (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))
  (test (interp (castE 'Posn posn27)
                (list posn-class posn3D-class)
                (objV 'Object 'Object empty) (numV 0))
        (objV 'Posn 'Object (list (box (numV 2)) (box (numV 7)))))
  (test/exn (interp (castE 'Posn3D posn27)
                (list posn-class posn3D-class)
                (objV 'Object 'Object empty) (numV 0))
        "not a subclass")
;;Test Part3 ----------------------------------------
 (test (interp (if0E (numE 0) (numE 1) (numE 2))
               (list posn-class posn3D-class)
               (objV 'Object 'Object empty) (numV 0))
       (numV 1))  
 (test (interp (if0E (numE 0) posn531 posn27)
               (list posn-class posn3D-class)
               (objV 'Object 'Object empty) (numV 0))
       (objV 'Posn3D 'Posn (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))
 (test (interp (if0E (numE 1) posn531 posn27)
                (list posn-class posn3D-class)
                (objV 'Object 'Object empty) (numV 0))
        (objV 'Posn 'Object (list (box (numV 2)) (box (numV 7)))))
;;Test Part4 ----------------------------------------
  (test (interp-posn (newE 'Square (list (nullE) (numE 4))))                              ;;null as object variable Part4
        (objV 'Square 'Object (list (box (nullV)) (box (numV 4)))))
  (test (interp-posn (sendE square27-5 'area (nullE)))                                    ;;null as method argument but not used Part4
        (numV 25))
  (test (interp-posn (sendE square27-5 'perimeter (numE 5)))                              ;;method argument with type num, so cannot take null Part4
        (numV 20))
  (test (interp-posn (sendE square27-5 'areaObj (newE 'Length (list (numE 5)))))          ;;method argument with type object Part 4
        (numV 25))
  (test/exn (interp-posn (sendE square27-5 'areaObj (nullE)))                             ;;method argument with type object, so can take null but cannot use it Part4
        "not an object")
;;Test Part5 ----------------------------------------
  (test (interp-posn (setE posn27 'x (numE 5)))
        (objV 'Posn 'Object (list (box (numV 5)) (box (numV 7)))))
  
  (test (interp-posn (setE posn27 'y (numE 5)))
        (objV 'Posn 'Object (list (box (numV 2)) (box (numV 5)))))
  
  (test (interp-posn (sendE rectangle5-10 'area (numE 0)))
        (numV 50))
  (test (interp-posn (sendE rectangle5-10 'calc-bigger-area (numE 8)))                     ;;test case to demonstrate imperative update Part5
        (numV 80))
  
  (test/exn (interp-posn (setE (numE 10) 'x (numE 5)))
        "not an object")
  ;;Test Part6 ----------------------------------------
  (test (interp-posn (setE (newE 'Posn (list (numE 0) (numE 0))) 'x (numE 5)))
        (objV 'Posn 'Object (list (box (numV 5)) (box (numV 0))))))  