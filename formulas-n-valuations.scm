(use-modules (grand scheme))


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


(define (expressed-as-¬v& form)
  (match form
    ('⊥ `(& p (¬ p)))
    ((? name?) form)
    (('¬ p) `(¬ ,(expressed-as-¬v& p)))
    (('& p q) `(& ,(expressed-as-¬v& p) ,(expressed-as-¬v& q)))
    (('v p q) `(v ,(expressed-as-¬v& p) ,(expressed-as-¬v& q)))
    (('→ p q) `(v (¬ ,(expressed-as-¬v& p)) ,(expressed-as-¬v& q)))
    (('≡ p q) `(v (& ,(expressed-as-¬v& p) ,(expressed-as-¬v& q))
                  (& (¬ ,(expressed-as-¬v& p)) (¬ ,(expressed-as-¬v& q)))))))

(e.g. (expressed-as-¬v& '(v (→ p q) (≡ q r)))
      ===> (v (v (¬ p) q) (v (& q r) (& (¬ q) (¬ r)))))


(define (expressed-as-¬v form)
  (match form
    ('⊥ `(¬ (v p ('¬ p))))
    ((? name?) form)
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


(define (expressed-as-⊥→ form)
  (match form
    ('⊥ '⊥)
    ((? name?) form)
    (('¬ p) `(→ ,(expressed-as-⊥→ p) ⊥))
    (('v p q) `(→ (→ ,(expressed-as-⊥→ p) ⊥) ,(expressed-as-⊥→ q)))
    (('→ p q) `(→ ,(expressed-as-⊥→ p) ,(expressed-as-⊥→ q)))
    (otherwise (expressed-as-⊥→ (expressed-as-¬v form))))) ;; lazy again.

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


(define (value form #;under valuation)
  (match form
    ('⊥ #f)
    ((? name?) (assoc-ref valuation form))
    (('¬ p) (not (value p valuation)))
    (('& p q) (and (value p valuation) (value q valuation)))
    (('v p q) (or (value p valuation) (value q valuation)))
    (('→ p q) (or (not (value p valuation)) (value q valuation)))
    (('≡ p q) (equal? (value p valuation) (value q valuation)))))

(e.g. (value #;of '(→ (v p (¬ p)) (v q (¬ q))) #;under '((p . #t) (q . #f)))
      ===> #t)

(define (truth-table form)
  (map (lambda (valuation) `(,valuation ,(value form #;under valuation)))
         (all-valuations #;over (names #;in form))))

(e.g. (truth-table '(& p (v q (¬ r))))
 ===> ((((q . #t) (r . #t) (p . #t)) #t)
       (((q . #f) (r . #t) (p . #t)) #f)
       (((q . #t) (r . #f) (p . #t)) #t)
       (((q . #f) (r . #f) (p . #t)) #t)
       (((q . #t) (r . #t) (p . #f)) #f)
       (((q . #f) (r . #t) (p . #f)) #f)
       (((q . #t) (r . #f) (p . #f)) #f)
       (((q . #f) (r . #f) (p . #f)) #f)))


(define (have-same-values-in-all-models? form1 form2)
  (let* ((names (union (names form1) (names form2)))
         (truth-values (multicombinations '(#t #f) (length names)))
         (valuations (map (lambda (tv) (map cons names tv)) truth-values)))
    (every (lambda (valuation) (equal? (value form1 valuation)
                                  (value form2 valuation)))
           valuations)))

(e.g. (have-same-values-in-all-models? '(→ p q) '(v (¬ p) q)))
(e.g. (have-same-values-in-all-models? '(& p q) '(& q p))


(e.g. (have-same-values-in-all-models? 
       '(v (→ p q) (≡ q r))
       (expressed-as-¬v& '(v (→ p q) (≡ q r)))))

(e.g. (have-same-values-in-all-models? 
       '(v (→ p q) (≡ q r))
       (expressed-as-¬v '(v (→ p q) (≡ q r)))))

(e.g. (have-same-values-in-all-models? 
       '(v (→ p q) (≡ q r))
       (expressed-as-⊥→ '(v (→ p q) (≡ q r)))))
