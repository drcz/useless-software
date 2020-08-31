(use-modules (grand scheme))
(define empty? null?)


(define name? symbol?)

(define (formula? x)
  (match x
    ((? name?) #t)
    (('¬ f) (and (formula? f)))
    (('& f f*) (and (formula? f) (formula? f*)))
    (('v f f*) (and (formula? f) (formula? f*)))
    (('→ f f*) (and (formula? f) (formula? f*)))
    (('≡ f f*) (and (formula? f) (formula? f*)))
    (otherwise #f)))


(define (contradicts? f f*)
  (or (equal? f `(¬ ,f*)) (equal? `(¬ ,f) f*)))

(e.g. (not (contradicts? 'p '(¬ (→ p q)))))
(e.g. (contradicts? '(¬ (→ p q)) '(→ p q)))

(define (has-contradiction? branch)
  (any (lambda (f) (any (lambda (f*) (contradicts? f f*)) branch)) branch))

(e.g. (has-contradiction? '(p q (¬ p) r)))
(e.g. (not (has-contradiction? '(q (¬ p) r))))


(define (literal? x)
  (match x
    ((? name?) #t)
    (('¬ (? name?)) #t)
    (_ #f)))

(e.g. (literal? 'p))
(e.g. (literal? '(¬ p)))
(e.g. (not (literal? '(v p q))))

;;;; three tableaux-specific thingies...

(define (nonbranching-successors #;for formula)
  (match formula
    (('¬ ('¬ f)) `(,f))
    (('& f f*) `(,f ,f*))
    (('¬ ('v f f*)) `((¬ ,f) (¬ ,f*)))
    (('¬ ('→ f f*)) `(,f (¬ ,f*)))
    (_ '())))

(e.g. (nonbranching-successors '(& (→ p q) (→ q p)))
      ===> ((→ p q) (→ q p)))


(define (branching-successors #;for formula)
  (match formula
    (('¬ ('& f f*)) `(((¬ ,f)) (('¬ ,f*))))
    (('v f f*) `((,f) (,f*)))
    (('→ f f*) `(((¬ ,f)) (,f*)))
    (('≡ f f*) `((,f ,f*) ((¬ ,f) (¬ ,f*))))
    (('¬ ('≡ f f*)) `(((¬ ,f) ,f*) (,f (¬ ,f*))))
    (_ '())))

(e.g. (branching-successors '(v (→ p q) (→ q p)))
      ===> (((→ p q)) ((→ q p))))
(e.g. (branching-successors '(≡ (→ p q) (→ q p)))
      ===> (((→ p q) (→ q p))
            ((¬ (→ p q)) (¬ (→ q p)))))


(define (branching? formula)
  (and (not (literal? formula))
       (not (empty? (branching-successors formula)))))

(e.g. (branching? '(→ p q)))
(e.g. (not (branching? '(¬ (→ p q)))))


;;; the magic happens here:

(define (counterexamples-for formula #;given hypotheses)
  (let tableaux ((pending `(,@hypotheses (¬ ,formula)))
                 (literals '()))
    (let* ((new-literals pending* (partition literal? pending))
           (literals* (union literals new-literals)))
      (cond ((has-contradiction? literals*)
             '()) ;; no counterexamples \o/
          ((empty? pending*)
           `(,literals*)) ;; a counterexample :o
          (else (let* ((branching nonbranching (partition branching? pending*)))
                  (cond ((not (empty? nonbranching))
                         (tableaux `(,@branching
                                     ,@(append-map nonbranching-successors
                                                   nonbranching))
                                   literals*))
                        ((not (empty? branching))
                         (let* (((f . branching*) branching)
                                ((fs0 fs1) (branching-successors f))
                                (pending0 `(,@branching* ,@fs0))
                                (pending1 `(,@branching* ,@fs1)))
                           (union (tableaux pending0 literals*)
                                  (tableaux pending1 literals*))))
                        (else `(,literals*))))))))) ;; a counterexample too!

(e.g. (counterexamples-for '(v (→ p q) (→ q p)) '()) ===> ())
(e.g. (counterexamples-for '(≡ (≡ p q) r) '((≡ p (≡ p r))))
      ===> ( (q r (¬ p)) #;and ((¬ q) r p) ))


(define (theorem? formula) (empty? (counterexamples-for formula '())))

(e.g. (theorem? '(v p (¬ p))))
(e.g. (theorem? '(¬ (& p (¬ p)))))
(e.g. (theorem? '(≡ (→ p q) (→ (¬ q) (¬ p)))))



