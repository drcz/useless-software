(use-modules (grand scheme))

;;; Bonus. [not too] effective [sort of] enumeration for "⊥→-formulas"
;;; over some fixed set of propositional names:

(define (zigzag n) (map (lambda (i) `(,i ,(- n i))) (iota (+ 1 n))))

(e.g. (zigzag 2) ===> ((0 2) (1 1) (2 0)))
(e.g. (zigzag 3) ===> ((0 3) (1 2) (2 1) (3 0)))
(e.g. (zigzag 4) ===> ((0 4) (1 3) (2 2) (3 1) (4 0)))


(define/memoized (all-formulas #;over names #;with n #;arrows)
  (if (= n 0)
      `(⊥ . ,names)
      (append-map (lambda ((d d*))
                    (let* ((ls (all-formulas names d))
                           (rs (all-formulas names d*)))
                      (map (lambda (as) `(→ . ,as)) (cartesian-product ls rs))))
                  (zigzag (- n 1)))))

(e.g. (all-formulas '(p q) 0) ===> (⊥ p q))

(e.g. (all-formulas '(p) 1) ===> ((→ ⊥ ⊥) (→ p ⊥) (→ ⊥ p) (→ p p)))

(e.g. (all-formulas '(p) 2) ===> ((→ ⊥ (→ ⊥ ⊥)) (→ p (→ ⊥ ⊥)) (→ ⊥ (→ p ⊥))
                                  (→ p (→ p ⊥)) (→ ⊥ (→ ⊥ p)) (→ p (→ ⊥ p))
                                  (→ ⊥ (→ p p)) (→ p (→ p p)) (→ (→ ⊥ ⊥) ⊥)
                                  (→ (→ p ⊥) ⊥) (→ (→ ⊥ p) ⊥) (→ (→ p p) ⊥)
                                  (→ (→ ⊥ ⊥) p) (→ (→ p ⊥) p) (→ (→ ⊥ p) p)
                                  (→ (→ p p) p)))

(e.g. (all-formulas '(p) 3)
      ===> ((→ ⊥ (→ ⊥ (→ ⊥ ⊥))) (→ p (→ ⊥ (→ ⊥ ⊥))) (→ ⊥ (→ p (→ ⊥ ⊥)))
            (→ p (→ p (→ ⊥ ⊥))) (→ ⊥ (→ ⊥ (→ p ⊥))) (→ p (→ ⊥ (→ p ⊥)))
            (→ ⊥ (→ p (→ p ⊥))) (→ p (→ p (→ p ⊥))) (→ ⊥ (→ ⊥ (→ ⊥ p)))
            (→ p (→ ⊥ (→ ⊥ p))) (→ ⊥ (→ p (→ ⊥ p))) (→ p (→ p (→ ⊥ p)))
            (→ ⊥ (→ ⊥ (→ p p))) (→ p (→ ⊥ (→ p p))) (→ ⊥ (→ p (→ p p)))
            (→ p (→ p (→ p p))) (→ ⊥ (→ (→ ⊥ ⊥) ⊥)) (→ p (→ (→ ⊥ ⊥) ⊥))
            (→ ⊥ (→ (→ p ⊥) ⊥)) (→ p (→ (→ p ⊥) ⊥)) (→ ⊥ (→ (→ ⊥ p) ⊥))
            (→ p (→ (→ ⊥ p) ⊥)) (→ ⊥ (→ (→ p p) ⊥)) (→ p (→ (→ p p) ⊥))
            (→ ⊥ (→ (→ ⊥ ⊥) p)) (→ p (→ (→ ⊥ ⊥) p)) (→ ⊥ (→ (→ p ⊥) p))
            (→ p (→ (→ p ⊥) p)) (→ ⊥ (→ (→ ⊥ p) p)) (→ p (→ (→ ⊥ p) p))
            (→ ⊥ (→ (→ p p) p)) (→ p (→ (→ p p) p)) (→ (→ ⊥ ⊥) (→ ⊥ ⊥))
            (→ (→ p ⊥) (→ ⊥ ⊥)) (→ (→ ⊥ p) (→ ⊥ ⊥)) (→ (→ p p) (→ ⊥ ⊥))
            (→ (→ ⊥ ⊥) (→ p ⊥)) (→ (→ p ⊥) (→ p ⊥)) (→ (→ ⊥ p) (→ p ⊥))
            (→ (→ p p) (→ p ⊥)) (→ (→ ⊥ ⊥) (→ ⊥ p)) (→ (→ p ⊥) (→ ⊥ p))
            (→ (→ ⊥ p) (→ ⊥ p)) (→ (→ p p) (→ ⊥ p)) (→ (→ ⊥ ⊥) (→ p p))
            (→ (→ p ⊥) (→ p p)) (→ (→ ⊥ p) (→ p p)) (→ (→ p p) (→ p p))
            (→ (→ ⊥ (→ ⊥ ⊥)) ⊥) (→ (→ p (→ ⊥ ⊥)) ⊥) (→ (→ ⊥ (→ p ⊥)) ⊥)
            (→ (→ p (→ p ⊥)) ⊥) (→ (→ ⊥ (→ ⊥ p)) ⊥) (→ (→ p (→ ⊥ p)) ⊥)
            (→ (→ ⊥ (→ p p)) ⊥) (→ (→ p (→ p p)) ⊥) (→ (→ (→ ⊥ ⊥) ⊥) ⊥)
            (→ (→ (→ p ⊥) ⊥) ⊥) (→ (→ (→ ⊥ p) ⊥) ⊥) (→ (→ (→ p p) ⊥) ⊥)
            (→ (→ (→ ⊥ ⊥) p) ⊥) (→ (→ (→ p ⊥) p) ⊥) (→ (→ (→ ⊥ p) p) ⊥)
            (→ (→ (→ p p) p) ⊥) (→ (→ ⊥ (→ ⊥ ⊥)) p) (→ (→ p (→ ⊥ ⊥)) p)
            (→ (→ ⊥ (→ p ⊥)) p) (→ (→ p (→ p ⊥)) p) (→ (→ ⊥ (→ ⊥ p)) p)
            (→ (→ p (→ ⊥ p)) p) (→ (→ ⊥ (→ p p)) p) (→ (→ p (→ p p)) p)
            (→ (→ (→ ⊥ ⊥) ⊥) p) (→ (→ (→ p ⊥) ⊥) p) (→ (→ (→ ⊥ p) ⊥) p)
            (→ (→ (→ p p) ⊥) p) (→ (→ (→ ⊥ ⊥) p) p) (→ (→ (→ p ⊥) p) p)
            (→ (→ (→ ⊥ p) p) p) (→ (→ (→ p p) p) p)))

;;; etc...
