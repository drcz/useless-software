(use-modules (grand scheme))

(define (reduce kons xs) ;; sligthly different from right-fold
  (match xs
    ((x x*) (kons x x*))
    ((x . xs*) (kons x (reduce kons xs*)))))

(e.g. (reduce (lambda (h t) `(& ,h ,t)) '(p q r s))
      ===> (& p (& q (& r s))))

(e.g. (reduce + '(1 2 3 4)) ===> 10)


;;; "syntax" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define name? symbol?)

(define (formula? x)
  (match x
    ('⊥ #t)
    ((? name?) #t)
    (('¬ f) (and (formula? f)))
    (('& f f*) (and (formula? f) (formula? f*)))
    (('v f f*) (and (formula? f) (formula? f*)))
    (('→ f f*) (and (formula? f) (formula? f*)))
    (('≡ f f*) (and (formula? f) (formula? f*)))
    (otherwise #f)))

(e.g. (every formula? '(p
                        (→ p q)
                        (v (→ p q) (→ q p))
                        (& p (& (¬ q) (¬ r))))))

(e.g. (not (formula? '(→ q))))
(e.g. (not (formula? '(v p q r))))


(define (names #;in formula)
  (match formula
    ('⊥ '())
    ((? name?) `(,formula))
    (('¬ f) (names #;in f))
    ((_ f f*) (union (names #;in f) (names #;in f*)))))

(e.g. (names #;in '(v (& p (& (¬ q) (¬ r))) (→ r (≡ p2 ⊥))))
      ===> (p2 q r p))


(define (expressed-as-¬v& formula)
  (match formula
    ('⊥ `(& p (¬ p)))
    ((? name?) formula)
    (('¬ p) `(¬ ,(expressed-as-¬v& p)))
    (('& p q) `(& ,(expressed-as-¬v& p) ,(expressed-as-¬v& q)))
    (('v p q) `(v ,(expressed-as-¬v& p) ,(expressed-as-¬v& q)))
    (('→ p q) `(v (¬ ,(expressed-as-¬v& p)) ,(expressed-as-¬v& q)))
    (('≡ p q) `(v (& ,(expressed-as-¬v& p) ,(expressed-as-¬v& q))
                  (& (¬ ,(expressed-as-¬v& p)) (¬ ,(expressed-as-¬v& q)))))))

(e.g. (expressed-as-¬v& '(v (→ p q) (≡ q r)))
      ===> (v (v (¬ p) q) (v (& q r) (& (¬ q) (¬ r)))))


(define (expressed-as-¬v formula)
  (match formula
    ('⊥ `(¬ (v p ('¬ p))))
    ((? name?) formula)
    (('¬ p) `(¬ ,(expressed-as-¬v p)))
    (('& p q) `(¬ (v (¬ ,(expressed-as-¬v p)) (¬ ,(expressed-as-¬v q)))))
    (('v p q) `(v ,(expressed-as-¬v p) ,(expressed-as-¬v q)))
    (('→ p q) `(v (¬ ,(expressed-as-¬v p)) ,(expressed-as-¬v q)))
    (('≡ p q) (expressed-as-¬v `(& (→ ,p ,q) (→ ,q , p)))))) ;; we're just lazy.

(e.g. (expressed-as-¬v '(v (→ p q)
                           (≡ q r)))
      ===> (v (v (¬ p) q)
              (¬ (v (¬ (v (¬ q) r))
                    (¬ (v (¬ r) q))))))


(define (expressed-as-⊥→ formula)
  (match formula
    ('⊥ '⊥)
    ((? name?) formula)
    (('¬ p) `(→ ,(expressed-as-⊥→ p) ⊥))
    (('v p q) `(→ (→ ,(expressed-as-⊥→ p) ⊥) ,(expressed-as-⊥→ q)))
    (('→ p q) `(→ ,(expressed-as-⊥→ p) ,(expressed-as-⊥→ q)))
    (otherwise (expressed-as-⊥→ (expressed-as-¬v formula))))) ;; lazy again.

(e.g. (expressed-as-⊥→ '(v (→ p q) (≡ q r)))
      ===> (→ (→ (→ p q) ⊥)
              (→ (→ (→ (→ (→ (→ (→ q ⊥) ⊥) r) ⊥) ⊥)
                    (→ (→ (→ (→ r ⊥) ⊥) q) ⊥)) ⊥)))



;;; "semantics" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define truth-value? boolean?)

(define (valuation? x)
  (and (list? x)
       (every pair? x)
       (every (lambda ((n . tv)) (and (name? n) (truth-value? tv))) x)))

(e.g. (valuation? '((p . #t) (q . #f))))
(e.g. (not (valuation? '(p whatever))))


(define (all-valuations #;over names)
  (let* ((truth-values (multicombinations '(#t #f) (length names)))
         (valuations (map (lambda (tv) (map cons names tv)) truth-values)))
    valuations))

(e.g. (all-valuations '(p q))
      ===> (((p . #t) (q . #t))
            ((p . #f) (q . #t))
            ((p . #t) (q . #f))
            ((p . #f) (q . #f))))


(define (value formula #;under valuation)
  (match formula
    ('⊥ #f)
    ((? name?) (assoc-ref valuation formula))
    (('¬ p) (not (value p valuation)))
    (('& p q) (and (value p valuation) (value q valuation)))
    (('v p q) (or (value p valuation) (value q valuation)))
    (('→ p q) (or (not (value p valuation)) (value q valuation)))
    (('≡ p q) (equal? (value p valuation) (value q valuation)))))

(e.g. (value #;of '(→ (v p (¬ p)) (v q (¬ q))) #;under '((p . #t) (q . #f)))
      ===> #t)

(define (truth-table formula)
  (map (lambda (valuation) `(,valuation ,(value formula #;under valuation)))
         (all-valuations #;over (names #;in formula))))

(e.g. (truth-table '(& p (v q (¬ r))))
 ===> ((((q . #t) (r . #t) (p . #t)) #t)
       (((q . #f) (r . #t) (p . #t)) #f)
       (((q . #t) (r . #f) (p . #t)) #t)
       (((q . #f) (r . #f) (p . #t)) #t)
       (((q . #t) (r . #t) (p . #f)) #f)
       (((q . #f) (r . #t) (p . #f)) #f)
       (((q . #t) (r . #f) (p . #f)) #f)
       (((q . #f) (r . #f) (p . #f)) #f)))


(define (have-same-values-in-all-valuations? formula formula*)
  (every (lambda (valuation) (equal? (value formula valuation)
                                (value formula* valuation)))
         (all-valuations #;over (union (names formula) (names formula*)))))

(e.g. (have-same-values-in-all-valuations? '(→ p q) '(v (¬ p) q)))
(e.g. (have-same-values-in-all-valuations? '(& p q) '(& q p)))


(e.g. (have-same-values-in-all-valuations? 
       '(v (→ p q) (≡ q r))
       (expressed-as-¬v& '(v (→ p q) (≡ q r)))))

(e.g. (have-same-values-in-all-valuations? 
       '(v (→ p q) (≡ q r))
       (expressed-as-¬v '(v (→ p q) (≡ q r)))))

(e.g. (have-same-values-in-all-valuations? 
       '(v (→ p q) (≡ q r))
       (expressed-as-⊥→ '(v (→ p q) (≡ q r)))))


(define (models #;for formula)
  (filter (lambda (valuation) (value formula #;under valuation))
          (all-valuations #;over (names #;in formula))))

(e.g. (models '(& (→ p q) q))
      ===> (((q . #t) (p . #t))
            ((q . #t) (p . #f))))


;;; "semantic" way of converting into Disjunctive Normal Form:

(define (DNF #;for formula)
  (define (literal #;from (name . truth-value))
    (if truth-value name #;else `(¬ ,name)))

  (define (clause #;from valuation)
    (reduce (lambda (f f*) `(& ,f ,f*)) (map literal valuation)))

  (reduce (lambda (f f*) `(v ,f ,f*)) (map clause (models formula))))

(e.g. (DNF '(→ p q))
      ===> (v (& q p) (v (& q (¬ p)) (& (¬ q) (¬ p)))))

(e.g. (DNF '(& p (v q (¬ r))))
      ===> (v (& q (& r p)) (v (& q (& (¬ r) p)) (& (¬ q) (& (¬ r) p)))))

(e.g. (have-same-values-in-all-valuations? '(& p (v q (¬ r)))
                                           (DNF '(& p (v q (¬ r))))))
