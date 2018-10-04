#lang racket
(require parser-tools/lex
         parser-tools/yacc)
(require "declarations.rkt")
(require "utilities.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;      Assignment 2       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-syntax lc
  (syntax-rules (: <- @)
    [(lc expr : var <- drawn-from) (map (lambda (var) expr) drawn-from)]
    [(lc expr : @ guard) (if guard (list expr) `())]
    [(lc expr : @ guard  qualifier ...) 
     (append* (lc (lc expr : qualifier ...) : @ guard))]
    [(lc expr : var <- drawn-from  qualifier ...) 
     (append* (lc (lc expr :  qualifier ... ) : var <- drawn-from))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (qsort l)
  (cond [(null? l) '()]
        [else (let ((lows (lc x : x <- (cdr l) @(< x (car l))))
                    (highs (lc x : x <- (cdr l) @(> x (car l)))))
                (append (qsort lows) (list (car l))
                        (qsort highs)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (nullable t)
  (cond [(Epsilon? t) #t]
        [(Literal? t) #f]
        [(Or? t) (or (nullable (Or-t1 t)) (nullable (Or-t2 t)))]
        [(Then? t) (and (nullable (Then-t1 t)) (nullable (Then-t2 t)))]
        [(Star? t) #t]
        ))

  
                       
(define (buildNullable t)
  (define (build-nullable-helper t)
    (cond [(Epsilon? t) (cons (list (cons (Epsilon-n t) #t)) #t)]
          [(Literal? t) (cons (list (cons (Literal-n t) #f)) #f)]
          [(Or? t) (let* ( [t1 (build-nullable-helper (Or-t1 t))]
                           [t2 (build-nullable-helper (Or-t2 t))]
                           )
                     (cons (append (car t1) (list (cons (Or-n t) (or (cdr t1) (cdr t2)))) (car t2))
                      (or (cdr t1) (cdr t2))))]
           [(Then? t) (let* ( [t1 (build-nullable-helper (Then-t1 t))]
                           [t2 (build-nullable-helper (Then-t2 t))]
                           )
                     (cons (append (car t1) (list (cons (Then-n t) (and (cdr t1) (cdr t2)))) (car t2))
                     (and (cdr t1) (cdr t2))))]
           [(Star? t) (cons (cons (cons (Star-n t) #t) 
                                  (car (build-nullable-helper (Star-t t))))
                            #t) ]
          
  ))
  (car (build-nullable-helper t))
  )
(define (buildFirst t)
  (define (build-first-helper t)
    (cond [(Epsilon? t) (cons (list (list (Epsilon-n t))) '())]
          [(Literal? t) (cons (list (cons (Literal-n t) (list (Literal-n t)))) (list (Literal-n t)))]
          [(Or? t) (let* ( [t1 (build-first-helper (Or-t1 t))]
                           [t2 (build-first-helper (Or-t2 t))]
                           )
                     (cons (append (car t1) (list (cons (Or-n t) (union (cdr t1) (cdr t2)))) (car t2))
                      (union (cdr t1) (cdr t2))))]
           [(Then? t) (let* ( [t1 (build-first-helper (Then-t1 t))]
                           [t2 (build-first-helper (Then-t2 t))]
                           )
                    (if (nullable (Then-t1 t))  (cons (append (car t1) (list (cons (Then-n t) (union (cdr t1) (cdr t2)))) (car t2))
                      (union (cdr t1) (cdr t2)))
                         (cons (append (car t1) (list (cons (Then-n t) (cdr t1))) (car t2))
                      (cdr t1)) )
                        )
                        ]
           [(Star? t) (let* ( [t1 (build-first-helper (Star-t t))] )
             (cons (cons (cons (Star-n t) (cdr t1)) 
                                  (car t1))
                            (cdr t1)))
                      ]
          
  ))
  (car (build-first-helper t))
  )
(define (union l1 l2)
(define (remove-duplicates l1)
 (rem-dup-helper l1 '())
  )
  (define (rem-dup-helper l1 l2)
  (cond [(null? l1) (reverse l2)]
        [(exists? (car l1) l2) (rem-dup-helper (cdr l1) l2)]
        [else (rem-dup-helper (cdr l1) (cons (car l1) l2))]
        ))

(define (exists? x l2)
  (cond [(null? l2) #f]
        [else (if (equal? (car l2) x) #t (exists? x (cdr l2)))]
        ))
  (remove-duplicates (append l1 l2)))

(define (buildLast t)
  (define (build-last-helper t)
    (cond [(Epsilon? t) (cons (list (list (Epsilon-n t))) '())]
          [(Literal? t) (cons (list (cons (Literal-n t) (list (Literal-n t)))) (list (Literal-n t)))]
          [(Or? t) (let* ( [t1 (build-last-helper (Or-t1 t))]
                           [t2 (build-last-helper (Or-t2 t))]
                           )
                     (cons (append (car t1) (list (cons (Or-n t) (union (cdr t1) (cdr t2)))) (car t2))
                      (union (cdr t1) (cdr t2))))]
           [(Then? t) (let* ( [t1 (build-last-helper (Then-t1 t))]
                           [t2 (build-last-helper (Then-t2 t))]
                           )
                    (if (nullable (Then-t2 t))  (cons (append (car t1) (list (cons (Then-n t) (union (cdr t1) (cdr t2)))) (car t2))
                      (union (cdr t1) (cdr t2)))
                         (cons (append (car t1) (list (cons (Then-n t) (cdr t2))) (car t2))
                      (cdr t2)) )
                        )
                        ]
           [(Star? t) (let* ( [t1 (build-last-helper (Star-t t))] )
             (cons (cons (cons (Star-n t) (cdr t1)) 
                                  (car t1))
                            (cdr t1)))
                      ]
          
  ))
  (car (build-last-helper t))
  )
 
 (define (present? x l)
   (cond [(null? l) #f]
         [else (if (equal? (car l) x) #t (present? x (cdr l)))]
         ))
(define (intersection l1 l2)
  (cond [(null? l1) l1]
        [else (if (present? (car l1) l2) (cons (car l1) (intersection (cdr l1) (remove (car l1) l2)))
                                         (intersection (cdr l1) l2))]))
                                               
 
(define (lastpos n lplist)
  (cond [(null? lplist) "Error"]
        [else (if (equal? (caar lplist) n) (cdar lplist) (lastpos n (cdr lplist)))]
        ))

(define (fpos n fplist)
  (cond [(null? fplist) "Error"]
        [else (if (equal? (caar fplist) n) (cdar fplist) (fpos n (cdr fplist)))]
        ))

(define (followpos n follow-pos-list)
  (cond [(null? follow-pos-list) '()]
        [else (if (equal? (caar follow-pos-list) n) (cdar follow-pos-list) (followpos n (cdr follow-pos-list)))]
        ))

(define (get-n t)
    (cond [(Epsilon? t) (Epsilon-n t) ]
        [(Literal? t) (Literal-n t)]
        [(Or? t) (Or-n t)]
        [(Then? t) (Then-n t)]
        [(Star? t) (Star-n t)]
        ))
 (define (leafNumbers t)
    (cond [(Literal? t) (if (equal? (Literal-c t) "#" ) '() (list (Literal-n t)))]
          [(Epsilon? t) '()]
          [(Or? t) (append (leafNumbers (Or-t1 t)) (leafNumbers (Or-t2 t)))]
          [(Then? t) (append (leafNumbers (Then-t1 t)) (leafNumbers (Then-t2 t)))]
          [(Star? t) (leafNumbers (Star-t t))]
          ))

(define (buildFollow t)

  (define fplist (buildFirst t))
  (define lplist (buildLast t))
  
  (define (buildCheck t)
    (cond
      [(Then? t) (append (buildCheck (Then-t2 t)) (buildCheck (Then-t1 t)) (list (cons (lastpos (get-n (Then-t1 t)) lplist) (fpos (get-n (Then-t2 t)) fplist))))]
      [ (Star? t) (append (buildCheck (Star-t t)) (list (cons (lastpos (get-n (Star-t t)) lplist) (fpos (get-n (Star-t t)) fplist))))]
      [(Or? t) (append  (buildCheck (Or-t2 t)) (buildCheck (Or-t1 t)))]
      [(Literal? t) '()]
      [(Epsilon? t) '()]
      
      ))


(define (buildAnswer leafs check-list)
  (cond [(null? leafs) '()]
        [else (cons (cons (car leafs) (generate (car leafs) check-list)) (buildAnswer (cdr leafs) check-list))]
        ))
  (define (generate x l)
    (cond [(null? l) '()]
          [else (if (present? x (caar l)) (append (cdar l) (generate x (cdr l))) (generate x (cdr l)))]

          ))
  
  (define (process-answer ll)
    (cond [(null? ll) ll]
          [else (if (<= (length (car ll)) 1) (process-answer (cdr ll))
                    (cons (car ll) (process-answer (cdr ll)) ))]
          ))
   (let* ( [l (process-answer (buildAnswer (leafNumbers t) (buildCheck t)))])
     (map (lambda (x) (cons (car x) (qsort (cdr x)))) l)
  ))
(define (detect-sym t)

(define (remove-duplicates l1)
 (rem-dup-helper l1 '())
  )
  (define (rem-dup-helper l1 l2)
  (cond [(null? l1) (reverse l2)]
        [(exists? (car l1) l2) (rem-dup-helper (cdr l1) l2)]
        [else (rem-dup-helper (cdr l1) (cons (car l1) l2))]
        ))

(define (exists? x l2)
  (cond [(null? l2) #f]
        [else (if (equal? (car l2) x) #t (exists? x (cdr l2)))]
        ))

(define (detect-symbols t)
  (cond
    [(Then? t)  (append (detect-symbols (Then-t1 t)) (detect-symbols (Then-t2 t)))]
    [(Or? t)    (append (detect-symbols (Or-t1 t)) (detect-symbols (Or-t2 t)))]
    [(Star? t)  (detect-symbols (Star-t t))]
    [(Literal? t) (list (Literal-c t))]
    [(Epsilon? t) '()]
    ))
(remove-duplicates (detect-symbols t)))

(define (leafGen t)
  (cond
    [(Then? t)  (append (leafGen (Then-t1 t)) (leafGen (Then-t2 t)))]
    [(Or? t)    (append (leafGen (Or-t1 t)) (leafGen (Or-t2 t)))]
    [(Star? t)  (leafGen (Star-t t))]
    [(Literal? t) (list (cons (Literal-n t) (list (Literal-c t))))]
    [(Epsilon? t) '()]
    ))  

(define (null-remover ll)
  (cond [(null? ll) '()]
        [else (if (null? (car ll)) (null-remover (cdr ll)) (cons (car ll) (null-remover (cdr ll))))]
        ))

(define (null-trans-remover listoftransitions)
  (cond [(null? listoftransitions) '()]
        [else (if (null? (Trans-final (car listoftransitions))) (null-trans-remover (cdr listoftransitions))
                  (cons (car listoftransitions) (null-trans-remover (cdr listoftransitions))))]
))




(define (group node symbols leafs)
      
  
  (define (grp-sym sym node)
  (define (leaf-process leafs)
          
    (define (leaf-process-helper leafs)
      (cond
        [(null? leafs) '()]
        [else (if (equal? (cadar leafs) sym) (cons (caar leafs) (leaf-process-helper (cdr leafs)))
                  (leaf-process-helper (cdr leafs)))]
        ))
    (cons sym (leaf-process-helper leafs)))
    (let* ((l (leaf-process leafs)))
      
      (cond [(null? (intersection (cdr l) node)) (cons sym '())]
            [else (cons sym (intersection node (cdr l)))]
            )))
      
      (cond [(null? symbols) '()]
            [else (cons (grp-sym (car symbols) node) (group node (cdr symbols) leafs))]
            ))
(define (process-current listofpairs)
  (cond   [(null? listofpairs) '(())]
          [(null? (cdr listofpairs)) (cons (list (caar listofpairs)) (list (cdar listofpairs)))]  
          [else
           (let* ([res (process-current (cdr listofpairs))])
             (cons (cons (caar listofpairs) (car res)) (cons (cdar listofpairs) (cdr res))))
           ]))

(define (remover l1 l2)
  (cond [(null? l1) l1]
        [else (if (present? (car l1) l2) (remover (cdr l1) l2)
                                         (cons (car l1) (remover (cdr l1) l2)))]
        ))
(define (repair intres)
  (cond [(null? intres) (cons '() '())]
        [else (let* ([newres (repair (cdr intres))])
                (cons (append (caar intres) (car newres)) (append (cdar intres) (cdr newres)))
                )]))
(define (process-group g)
  (cond [(null? g) '()]
        [else (if (null? (cdar g)) (process-group (cdr g)) (cons (car g) (process-group (cdr g))))]
        ))

(define (buildGraph reg)
  (let* ( [t (maketree reg)] 
          [first-pos-list (buildFirst t)]
          [last-pos-list (buildLast t)]
          [follow-pos-list (buildFollow t)]
          [green-node (fpos (get-n t) first-pos-list)]
          [leafs (leafGen t)]          
          [symbols (detect-sym t)]
          )
    
   (define (buildnode l)
     (cond [(null? l) l]
           [else (append (followpos (car l) follow-pos-list) (buildnode (cdr l)))] 
           ))
    
  (define (node&trans-builder check-node-list node-list trans-list )
    
    (define (convert startnode l)
      (cond [(null? l) '()]
            [else (let* ([newnode (remove-duplicates (buildnode (cdar l)))])
                    (cons (cons newnode (Trans startnode (caar l) newnode)) (convert startnode (cdr l))))]
            ))


    (define (build-for-one-node node)
      (process-current (convert node (process-group (group node symbols leafs)))))


  (cond [(null? check-node-list) (cons node-list trans-list)]
        [else (let* ([intres (map (lambda (x) (build-for-one-node x)) check-node-list) ]
                     [repair-res (repair intres)]
                     [notrepeatednodes (remover (car repair-res) node-list)]
                     [temp-node-list (append node-list notrepeatednodes)]
                     [temp-trans-list (append (cdr repair-res) trans-list)]
                     )

               ; (cons (append (car curr-res) (car intres)) (append (cdr curr-res) (cdr intres)))
                   (cond [(null? notrepeatednodes) (cons temp-node-list temp-trans-list)]
                         [else (node&trans-builder notrepeatednodes temp-node-list temp-trans-list)]
                     
                      ))]
        ))
        
    


  (let* ( [res (node&trans-builder (list green-node) (list green-node) '())])
    (define (is-red? node)
      (if (present? (- (get-n t) 1) node) #t #f))
    (define (find-red node-list)
      (cond [(null? node-list) '()]
            [else (if (is-red? (car node-list)) (cons (car node-list) (find-red (cdr node-list)))
                                                (find-red (cdr node-list)))]))
      
      
    (Graph green-node (null-remover (car res)) (null-trans-remover (cdr res)) (find-red (car res)) symbols) )
    ))

