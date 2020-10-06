;;; this one is loosely based on folklore.

(use-modules (grand scheme))
(define empty? null?)
(define ((equals? x) y) (equal? x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FORMULAS, AXIOMS, PROOFS (again)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name? symbol?)

(define (formula? x)
  (match x
    ('⊥ #t)
    ((? name?) #t)
    (('→ f f*) (and (formula? f) (formula? f*)))
    (_ #f)))

(define (names #;in formula)
  (match formula
    ('⊥ '())
    ((? name?) `(,formula))
    (('→ f f*) (union (names #;in f) (names #;in f*)))))

(e.g. (names #;in '(→ (→ p (→ q ⊥)) r)) ===> (r q p))

(define (axiom? x)
  (match x
    (('→ A ('→ B A)) ;;; Ax1
     (and (formula? A) (formula? B)))
    (('→ ('→ A ('→ B C)) ('→ ('→ A B) ('→ A C))) ;; Ax2
     (and (formula? A) (formula? B) (formula? C)))
    (('→ ('→ ('→ A '⊥) '⊥) A) ;; Ax3
     (and (formula? A)))
    (otherwise #f)))

(e.g. (axiom? '(→ p (→ (→ q ⊥) p)))) ;; Ax1 with A<-p, B<-q
(e.g. (axiom? '(→ (→ (→ (→ q q) ⊥) ⊥) (→ q q)))) ;; Ax3 with A<-(→ q q)
(e.g. (not (axiom? '(→ ⊥ p))))

(define (inference? x)
  (and (list? x)
       (not (empty? x))
       (every formula? x)))

(define (conclusion #;of inference) (last inference))

(define (all-subinferences #;of inference)
  (map (lambda (i) (take inference (+ 1 i))) (iota (length inference))))

(e.g. (all-subinferences '( (→ p (→ q p))
                            p
                            (→ q p)
                            (→ p q)
                            q ))
      ===> (((→ p (→ q p)))
            ((→ p (→ q p)) p)
            ((→ p (→ q p)) p (→ q p))
            ((→ p (→ q p)) p (→ q p) (→ p q))
            ((→ p (→ q p)) p (→ q p) (→ p q) q)))


(define (follows-by-MP? formula previous-formulas)
  (any (lambda (formula*)
         (and-let* ((('→ antecendent consequent) formula*))
           (and (equal? consequent formula)
                (any (equals? antecendent) previous-formulas)
                `(,formula* ,antecendent))))
       previous-formulas))

(e.g. (follows-by-MP? 'p '(q (→ q p))) ===> ((→ q p) q))
(e.g. (not (follows-by-MP? 'p '(r (→ q p)))))

(define (all-hypotheses #;in inference)
  (filter-map (lambda (subinference)
                (let* (((previous ... formula) subinference))
                  (and (not (axiom? formula))
                       (not (follows-by-MP? formula previous))
                       formula)))
              (all-subinferences inference)))

(e.g. (all-hypotheses '( (→ p (→ q p)) ;; 1. Ax1
                         p             ;; 2. Hyp
                         (→ q p)       ;; 3. MP 1,2
                         (→ p q)       ;; 4. Hyp
                         q ))          ;; 5. MP 2,4
      ===> ( p
             (→ p q) ))

(define (proof? x)
  (and (inference? x)
       (empty? (all-hypotheses x))))

(define (proof-→AA #;with A)
  `( (→ (→ ,A (→ (→ ,A ,A) ,A))
        (→ (→ ,A (→ ,A ,A)) (→ ,A ,A))) ; 1. Ax2
     (→ ,A (→ (→ ,A ,A) ,A))            ; 2. Ax1
     (→ (→ ,A (→ ,A ,A)) (→ ,A ,A))     ; 3. MP 1,2
     (→ ,A (→ ,A ,A))                   ; 4. Ax1
     (→ ,A ,A) ))                       ; 5. MP 3,4

(e.g. (proof? (proof-→AA 'p)))
(e.g. (not (proof? '(p (→ p q) q))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; EXHAUSTIVE SEARCH FOR PROOFS (beautiful terrible idea)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; first let's represent sequences of formulas over some names
;;; as parentheses-less strings:

(define (inference<-string str)
  (define (parsed-form str)
    (match str
      (('⊥ . str*) `(⊥ ,str*))
      (('→ . str*) (and-let* (((e str**) (parsed-form str*))
                              ((e* str***) (parsed-form str**)))
                     `((→ ,e ,e*) ,str***)))
      (((? name? n) . str*) `(,n ,str*))
      (_ #f)))
  (match (parsed-form str)
    (#f #f)
    ((f ()) `(,f))
    ((f str*) (and-let* ((fs (inference<-string str*)))
                `(,f . ,fs)))
    (_ #f)))


(e.g. (inference<-string '(→ → p q → → q ⊥ → p ⊥ → p p q))
      ===> ((→ (→ p q) (→ (→ q ⊥) (→ p ⊥)))
            (→ p p)
            q))

(e.g. (inference<-string '(→ → p)) ===> #f)


;;; now we need to know how to generate all finite strings over
;;; given (finite) alphabet:

(define (next #;after str #;over alphabet)
  (define (next-symbol/carry? #;after s)
    (let* ((i (list-index alphabet s))
           (l (length alphabet))
           (i* (remainder (+ i 1) l))
           (s* (list-ref alphabet i*))
           (c? (= (+ i 1) l)))
      `(,s* ,c?)))
  (match str
    (() `(,(first alphabet)))
    ((s . str*) (let (((s* carry?*) (next-symbol/carry? s)))
                  `(,s* . ,(if carry?* (next str* alphabet) str*))))))

(e.g. (next '() '(a b c)) ===> (a))
(e.g. (next '(b) '(a b c)) ===> (c))
(e.g. (next '(c c) '(a b c)) ===> (a a a))
(e.g. (next '(c c a) '(a b c)) ===> (a a b))

;;; got it, dude?

;;; it's "easy" to find the first (in the ordering above) proof for
;;; any formula given. though i wouldn't try it for non-axioms.

(define (shortest-proof #;for formula)
  (let ((alphabet `(⊥ → . ,(names formula))))
    (let loop ((try '()))
      (or (and-let* ((inference (inference<-string try))
                     (conclusion (conclusion inference))
                     ((equal? conclusion formula))
                     ((proof? inference)))
            inference)
          (loop (next try alphabet))))))

(e.g. (shortest-proof '(→ p (→ q p)))
      ===> ((→ p (→ q p))))


;;; one can also keep printing out all of the theorem...

(define (enumerate-theorems #;over names)
  (let ((alphabet `(⊥ → . ,names)))    
    (let loop ((str '()))
      (match (inference<-string str)
        ((? proof? p) (begin
                        (write `(theorem: ,(conclusion p)))
                        (newline)
                        (write 'PROOF:)
                        (newline)
                        (map (lambda (f) (write f) (newline)) p)
                        (write 'qed)
                        (newline)
                        (newline)
                        (loop (next str alphabet))))
        (_ (loop (next str alphabet)))))))

;;; NB if you're hardcore you can restrict to ones where
;;; (not (axiom? (conclusion p))). we tried and none was found
;;; in 10h time. so all the early proofs will be sequences of axioms.
;;; but anyway the point is not to run this program at all, duh!

(set-port-encoding! (current-output-port) "UTF-8")
(enumerate-theorems '(p))

;;; good night.
