;;; this stuff is loosely based on chapter 2 of Allan Ramsay's
;;; ``Formal Methods in Artificial Intelligence''.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(use-modules (grand scheme))
(define empty? null?)
(define ((equals? x) y) (equal? x y))

;;; to keep each file self-contained we'll repeat some definitions from
;;; previous sections...

;;; don't judge.
(define (every-map p? xs)
  (let em ((xs xs)
           (res '()))    
    (match xs
      (() res)
      ((x . xs*) (match (p? x)
                   (#f #f)
                   (v (em xs* `(,@res ,v))))))))

(e.g. (every-map (lambda (x) (and (> x 2) (* x x))) '(3 4 5)) ===> (9 16 25))
(e.g. (every-map (lambda (x) (and (> x 2) (* x x))) '(3 2 5)) ===> #f)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FORMULAS, AXIOMS, VALUES, TAUTOLOGIES.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name? symbol?)

(define (formula? x)
  (match x
    ('⊥ #t)
    ((? name?) #t)
    (('→ f f*) (and (formula? f) (formula? f*)))
    (_ #f)))

(e.g. (formula? '(→ p q)))
(e.g. (formula? '(→ (→ p q) (→ (→ q ⊥) (→ p ⊥)))))
(e.g. (not (formula? '(→ q))))
(e.g. (not (formula? '(→ p q r))))

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

;;; VALUATIONS and VALUES are the same as in formulas-n-valuations.scm
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
    (('→ p q) (or (not (value p valuation)) (value q valuation)))))

(e.g. (value '(→ p q) '((p . #f) (q . #t))) ===> #t)
(e.g. (value '(→ p q) '((p . #t) (q . #f))) ===> #f)

;;; you can check that axioms have value #t under any valuation:
(e.g. (every (lambda (v) (value '(→ (→ p (→ q r)) (→ (→ p q) (→ p r))) v))
             (all-valuations '(p q r))))
;;; we called such formulas TAUTOLOGIES (some call them ``valid'' but meh):
(define (tautology? formula)
  (every (lambda (valuation) (value formula valuation))
         (all-valuations #;over (names formula))))

(e.g. (tautology? '(→ p (→ q p))))
(e.g. (tautology? '(→ (→ (→ (→ p p) ⊥) ⊥) (→ p p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; INFERENCES, PROOFS.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (inference? x)
  (and (list? x)
       (not (empty? x))
       (every formula? x)))

(e.g. (inference? '((→ p (→ q p))
                    p
                    (→ q p)
                    (→ p q)
                    q)))

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
(e.g. (not (proof? '(p (→ p q) q)))) ;; hypotheses!


(define (relativized inference #;wrt hypothesis)
  (let ((hypotheses (all-hypotheses inference)))
    (append-map
     (lambda (subinference)
       (let* (((previous ... formula) subinference))
         (cond                     
          ((equal? formula hypothesis) ;;; we already know how to prove (→ A A):
           (proof-→AA formula))

          ((or (axiom? formula)  ;;; one-liners are even simpler:
               (member? formula hypotheses))
           `( ,formula                              ;; original one-liner,
              (→ ,formula (→ ,hypothesis ,formula)) ;; Ax1,
              (→ ,hypothesis ,formula) ))           ;; MP on the two above.

          (else ;;; formula is derived by MP then...
           (let* (((implication antecendent) (follows-by-MP? formula previous))
                  ;;; and we know we have these already relativized to:
                  (antecendent* `(→ ,hypothesis ,antecendent))
                  (implication* `(→ ,hypothesis ,implication))
                  ;;; and we want:
                  (formula* `(→ ,hypothesis ,formula)))
             `( (→ ,implication* (→ ,antecendent* ,formula*)) ;; that's Ax2 (!),
                (→ ,antecendent* ,formula*)  ;; MP on implication* and one above,
                ,formula* ))))))             ;; MP on antecentent* and one above.
     (all-subinferences inference))))

(e.g.
 (relativized '( (→ p (→ q p)) ;; 1. Ax1
                 p             ;; 2. Hyp (i)
                 (→ q p)       ;; 3. MP 1,2
                 (→ p q)       ;; 4. Hyp (ii)
                 q )           ;; 5. MP 2,4
              #;wrt '(→ p q)) ;; which was our hypothesis (ii)
 ===> ((→ p (→ q p))
       (→ (→ p (→ q p)) (→ (→ p q) (→ p (→ q p))))
       (→ (→ p q) (→ p (→ q p)))
       p
       (→ p (→ (→ p q) p))
       (→ (→ p q) p)
       (→ (→ (→ p q) (→ p (→ q p)))
          (→ (→ (→ p q) p) (→ (→ p q) (→ q p))))
       (→ (→ (→ p q) p) (→ (→ p q) (→ q p)))
       (→ (→ p q) (→ q p))
       (→ (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
          (→ (→ (→ p q) (→ (→ p q) (→ p q)))
             (→ (→ p q) (→ p q))))
       (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
       (→ (→ (→ p q) (→ (→ p q) (→ p q)))
          (→ (→ p q) (→ p q)))
       (→ (→ p q) (→ (→ p q) (→ p q)))
       (→ (→ p q) (→ p q))
       (→ (→ (→ p q) (→ p q))
          (→ (→ (→ p q) p) (→ (→ p q) q)))
       (→ (→ (→ p q) p) (→ (→ p q) q))
       (→ (→ p q) q)))
 
(e.g. (all-hypotheses (relativized '( (→ p (→ q p))
                                      p
                                      (→ q p)
                                      (→ p q)
                                      q )
                                   #;wrt '(→ p q)))
      ===> (p)) ;; so now only hypothesis (i) is left.


;;; after ~230 lines of definitions and examples we're ready to go with
;;; some new stuff...


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; METAINFERENCES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; we can make claims about existence of certain inferences.
;;; those claims we'll call JUDGEMENTS:
(define (judgement? x)
  (and-let* (((hypotheses '⊢ formula) x))
    (and (every formula? hypotheses)
         (formula? formula))))

(e.g. (judgement? '(() ⊢ (→ p p))))
;;; which reads: ``there exists a proof (inference with no hypotheses)
;;; concluding with (→ p p)'' -- and this one happens to be the case as we've
;;; already seen such a proof above.

;;; mind that a judgement doesn't have to be the case. however some obviously are,
;;; e.g. there's always a trivial proof of an axiom, or a hypothesis can be
;;; derived easily by simply placing it at the end of inference.
;;; we will call these JUSTIFIED judgements:
(define (justified? judgement)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (or (axiom? formula)
        (member? formula hypotheses))))

(e.g. (justified? '(() ⊢ (→ q (→ p q)))))
(e.g. (justified? '((q p) ⊢ (→ q (→ p q)))))
(e.g. (justified? '((q p) ⊢ p)))
(e.g. (not (justified? '((q p) ⊢ (→ p q)))))


;;; obviously when we have some actual inference, we can make a judgement
;;; about it easily:
(define (judgement<-inference inference)
  `(,(all-hypotheses inference) ⊢ ,(conclusion inference)))

(e.g. (judgement<-inference (proof-→AA 'p)) ===> (() ⊢ (→ p p)))

(e.g. (judgement<-inference '(p
                              (→ p q)
                              q)) ===> ((p (→ p q)) ⊢ q))


;;; given we know some inferences with fixed hypotheses exist, we can infer
;;; (ha!) the existence of other inferences from the same (or wider)
;;; hypotheses. we'll call these derivations metainferences, and will try
;;; doing things analoguosly to inferences:
(define (metainference? x)
  (and (list? x)
       (not (empty? x))
       (every judgement? x)))

(e.g. (metainference? '( ((p (→ p q)) ⊢ p)       ;; justified (hypothesis)
                         ((p (→ p q)) ⊢ (→ p q)) ;; justified (hypothesis)
                         ((p (→ p q)) ⊢ q) )))   ;; exists by MP

;;; nb we can use (conclusion _) here as well so we will refer to the last
;;; judgement of metainference as its CONCLUSION too. similarly we have
;;; submetainferences...
(define all-submetainferences all-subinferences)

;;; for some hypotheses Σ when we know (Σ ⊢ φ) and (Σ ⊢ (→ φ ψ)) both hold,
;;; we should be able to deduce (Σ ⊢ ψ) -- as we could concatenate inferences
;;; for φ and (→ φ ψ) and then append ψ which follows by MP.

(define (⊢-follows-by-MP? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ ('→ ant* con*)) judgement*))
             (and (equal? con* formula)
                  (subset? hypotheses* hypotheses)
                  (any (lambda (judgement**)
                         (and-let* (((hypotheses** '⊢ formula**) judgement**))
                           (and (equal? formula** ant*)
                                (subset? hypotheses** hypotheses*))))
                       previous-judgements))))
         previous-judgements)))

(e.g. (⊢-follows-by-MP? '((p (→ p q)) ⊢ q)
                        '( ((p (→ p q)) ⊢ p)
                           ((p (→ p q)) ⊢ (→ p q)))))

(e.g. (⊢-follows-by-MP? '((p r (→ p q)) ⊢ q)
                        '( ((p (→ p q)) ⊢ p)
                           ((p (→ p q) r) ⊢ (→ p q)))))

(e.g. (not (⊢-follows-by-MP? '((p r (→ p q)) ⊢ q)
                             '( ((p (→ p q) r) ⊢ p)
                                ((p (→ p q)) ⊢ (→ p q))))))
;;; excercise: why doesn't this last one follow?

;;; when we know (Σ ⊢ φ) then (Σ* ⊢ φ) if all hypotheses in Σ are also
;;; in Σ* (i.e. when (subset Σ Σ*)) -- we don't have to use all hypotheses
;;; in the inference so adding more doesn't affect the already established
;;; inference:
(define (⊢-follows-by-subset? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* formula)
                  (subset? hypotheses* hypotheses))))
         previous-judgements)))

(e.g. (⊢-follows-by-subset? '((p q r) ⊢ (→ p q))
                            '((   (q) ⊢ (→ p q)))))


;;; Now something Ramsay doesn't mention but clearly uses implicitly;
;;; when we know (Σ ⊢ φ) and (Σ* ⊢ ψi) for every ψi in Σ, we also must have
;;; (Σ** ⊢ φ) whenever Σ** ⊂ Σ. this allows to compose metainferences with
;;; nontrivial hypotheses "dependencies":

(define (⊢-follows-by-composition? judgement #;from previous-judgements)
  (define (enough-to-infer? formula #;given hypotheses #;wrt previous-judgements)
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* formula)
                  (subset? hypotheses* hypotheses))))
         previous-judgements))

  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* formula)
                  (every (lambda (hypothesis)
                           (enough-to-infer? hypothesis
                                             #;given hypotheses
                                             #;wrt previous-judgements))
                         hypotheses*))))
         previous-judgements)))

(e.g. (⊢-follows-by-composition? '((p q) ⊢ r)
                                 '( (            (p q) ⊢ (→ p q))
                                    (              (p) ⊢ (→ p p))
                                    (((→ p p) (→ p q)) ⊢ r))))


;;; There is a very useful result called Deduction Theorem, which
;;; states that if ((φ) ⊢ φ*) then (() ⊢ (→ φ φ*)), and more generally if
;;; Σ is Σ* with φ included (or using set-theoretic metaphor Σ = Σ* ∪ {φ})
;;; then whenever (Σ ⊢ φ*) we have (Σ* ⊢ (→ φ φ*)).
;;; This follows from the fact that we can always relativize inference
;;; we know exists from (Σ ⊢ φ*) with respect to φ.

(define (⊢-follows-by-DT? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ ('→ ant con)) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* con)
                  (member? ant hypotheses*)
                  (subset? (difference hypotheses* `(,ant)) hypotheses))))
         previous-judgements)))

(e.g. (⊢-follows-by-DT? '(() ⊢ (→ p q)) #;from '(((p) ⊢ q ))))
(e.g. (⊢-follows-by-DT? '((r) ⊢ (→ p q)) #;from '(((p) ⊢ q ))))
(e.g. (⊢-follows-by-DT? '((r) ⊢ (→ p q)) #;from '(((r p) ⊢ q ))))
(e.g. (not (⊢-follows-by-DT? '(() ⊢ (→ p q)) #;from '(((p r) ⊢ q )))))
;;; excercise: why doesn't the last one follow?

;;; judgements which are not justified or following by DT, MP, hypotheses
;;; or subset we'll call ASSERTIONS. we could call them ``hypotheses'' too,
;;; or even better ``⊢-hypotheses'', but we don't.

(define (all-assertions #;in metainference)
  (filter-map (lambda (submetainference)
                (let* (((previous ... judgement) submetainference))
                  (and (not (justified? judgement))
                       (not (⊢-follows-by-subset? judgement previous))
                       (not (⊢-follows-by-DT? judgement previous))
                       (not (⊢-follows-by-MP? judgement previous))
                       (not (⊢-follows-by-composition? judgement previous))
                       judgement)))
              (all-submetainferences metainference)))

(e.g. (all-assertions '( ((p (→ p q)) ⊢ q)
                         ((p (→ p q)) ⊢ p)
                         ((p (→ p q)) ⊢ r) ))
      ===> (((p (→ p q)) ⊢ q)
            ((p (→ p q)) ⊢ r)))

(e.g. (all-assertions '( ((p (→ p q)) ⊢ (→ p q)) ;; just.
                         ((p (→ p q)) ⊢ p)       ;; just.
                         ((p (→ p q)) ⊢ q)       ;; by MP
                         ((p (→ p q)) ⊢ r) ))    ;; wat?
      ===> (((p (→ p q)) ⊢ r)))

(e.g. (all-assertions '( (    (p (→ p q)) ⊢ (→ p q)) ;; just.
                         (    (p (→ p q)) ⊢ p)       ;; just.
                         (    (p (→ p q)) ⊢ q)       ;; by MP
                         ((p r (→ p q) s) ⊢ q) ))    ;; from above one.
      ===> ())


;;; a metainference with no assertions we'll call SUFFICIENT for no better name:
(define (sufficient? metainference) (empty? (all-assertions metainference)))

;;; and then a sufficient metainference where the conclusion claims existence
;;; of a proof (i.e. inference from no hypotheses) we'll call a METAPROOF:
(define (metaproof? metainference)
  (and-let* (((hypotheses '⊢ formula) (conclusion metainference)))
    (and (empty? hypotheses)
         (sufficient? metainference))))

(e.g. (metaproof? '( ((p (→ p ⊥)) ⊢ p)                       ;; just. (hyp)
                     ((p (→ p ⊥)) ⊢ (→ p ⊥))                 ;; just. (hyp)
                     ((p (→ p ⊥)) ⊢ ⊥)                       ;; by MP
                     (        (p) ⊢ (→ (→ p ⊥) ⊥))           ;; by DT
                     (         () ⊢ (→ p (→ (→ p ⊥) ⊥))) ))) ;; by DT
                     
;;; This is quite useful [well, not really].
;;; Insted of tedious ``actual proofs'' we can now use metaproofs, as they
;;; are similarly convincing [are they?], yet much shorter.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CONVINCING PEOPLE.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; ok given all these (⊢-follows-by-<something> _ #;from _) we can actually
;;; convert sufficient metainference into inference (and thus metaproof into
;;; proof). for convenience we'd like them to provide the judgements which
;;; they use for justification...

(define (⊢-follows-by-subset*? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* formula)
                  (subset? hypotheses* hypotheses)
                  judgement*)))
         previous-judgements)))

(e.g. (⊢-follows-by-subset*? '((p q r) ⊢ (→ p q))
                             '((   (q) ⊢ (→ p q))))
      ===> ((q) ⊢ (→ p q))) ;; easy.


(define (⊢-follows-by-DT*? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ ('→ ant con)) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* con)
                  (member? ant hypotheses*)
                  (subset? (difference hypotheses* `(,ant)) hypotheses)
                  `(,judgement* ,ant))))
         previous-judgements)))

(e.g. (⊢-follows-by-DT*? '((r) ⊢ (→ p q)) #;from '(((p) ⊢ q )))
      ===> (((p) ⊢ q) ;;; judgement used in derivation
            p))       ;;; and the hypothesis to relativize it with.


(define (⊢-follows-by-MP*? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ ('→ ant* con*)) judgement*))
             (and (equal? con* formula)
                  (subset? hypotheses* hypotheses)
                  (any (lambda (judgement**)
                         (and-let* (((hypotheses** '⊢ formula**) judgement**))
                           (and (equal? formula** ant*)
                                (subset? hypotheses** hypotheses*)
                                `(,judgement* ,judgement** ,con*))))
                       previous-judgements))))
         previous-judgements)))

(e.g. (⊢-follows-by-MP*? '((p r (→ p q)) ⊢ q)
                         '(   ((p (→ p q)) ⊢ p)
                            ((p (→ p q) r) ⊢ (→ p q))))
      ===> ( ((p (→ p q) r) ⊢ (→ p q)) ;; justifies implication
             ((p (→ p q)) ⊢ p)         ;; justifies antecentent
             q))                       ;; actual conclusion formula


;;; this version is slightly uglier but whenever a justification for
;;; composition is found, it returns a list of judgements allowing
;;; to infer it.
(define (⊢-follows-by-composition*? judgement #;from previous-judgements)

  (define (enough-to-infer formula #;given hypotheses #;wrt previous-judgements)
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* formula)
                  (subset? hypotheses* hypotheses)
                  judgement*)))
         previous-judgements))

  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*)
                      (_ (equal? formula* formula))
                      (justification-for-hypotheses*
                       (every-map (lambda (hypothesis)
                                    (enough-to-infer hypothesis
                                                     #;given hypotheses
                                                     #;wrt previous-judgements))
                                  hypotheses*)))
             `(,@justification-for-hypotheses* ,judgement*)))
         previous-judgements)))
         

(e.g. (⊢-follows-by-composition*? '((p q) ⊢ r)
                                 '( (            (p q) ⊢ (→ p q))
                                    (            (p q) ⊢ q)
                                    (              (p) ⊢ (→ p p))
                                    (((→ p p) (→ p q) q) ⊢ r)))
      ===> (((p) ⊢ (→ p p))   ;;; justifies first hypothesis
            ((p q) ⊢ (→ p q)) ;;; ... second ...
            ((p q) ⊢ q)       ;;; ... third ...
            (((→ p p) (→ p q) q) ⊢ r))) ;;; finally: justifies the initial frm.


;;; now we'll go through the inference judgement by judgement, each time
;;; generating the inference in question. on the last one, its inference
;;; is the one we're looking for.

;;; we assert (sufficient? metainference)
(define (inference<-metainference metainference) 
  (let next ((pending metainference)
             (constructed '())) ;; a list of (<judgement> . <inference>) pairs
    (if (empty? pending)
        (let* (((judgement . proof) (last constructed))) proof) ;; boom!
        ;; else:
        (let* (((judgement . pending*) pending)
               (previous (map first constructed))
               (inference
                (or 
                 ;;; justified judgements generate ``one-liners''
                 (and (justified? judgement)
                      (let* (((hypotheses '⊢ formula) judgement)) `(,formula)))
                 ;;; following by subset doesn't influence the inference,
                 ;;; i.e. it's the same as for ``parent judgement'':
                 (and-let* ((judgement*
                             (⊢-follows-by-subset*? judgement previous)))
                   (assoc-ref constructed judgement*))
                 ;;; following by composition requires concatenating all
                 ;;; inferences for hypotheses and the inference from them
                 ;;; to the formula that current judgement is about:
                 (and-let* ((judgements
                             (⊢-follows-by-composition*? judgement previous)))
                   (append-map (lambda (i) (assoc-ref constructed i)) judgements))
                 ;;; following by DT requires relativizing parent judgement's
                 ;;; inference wrt to [some] hypothesis:
                 (and-let* (((judgement* hypothesis*)
                             (⊢-follows-by-DT*? judgement previous))
                            (inference*
                             (assoc-ref constructed judgement*)))
                   (relativized inference* hypothesis*))
                 ;;; finally, following by MP requires inferences for implication
                 ;;; and for antecentent, followed by the conclusion alone:
                 (and-let* (((imp-judgement ant-judgement conclusion)
                             (⊢-follows-by-MP*? judgement previous))
                            (imp-inference
                             (assoc-ref constructed imp-judgement))
                            (ant-inference
                             (assoc-ref constructed ant-judgement)))
                   `(,@imp-inference
                     ,@ant-inference
                     ,conclusion)))))
          (next pending* `(,@constructed (,judgement . ,inference)))))))

(e.g. (let* ((metaproof '( ((p (→ p ⊥)) ⊢ p)
                           ((p (→ p ⊥)) ⊢ (→ p ⊥))
                           ((p (→ p ⊥)) ⊢ ⊥)
                           (        (p) ⊢ (→ (→ p ⊥) ⊥))
                           (         () ⊢ (→ p (→ (→ p ⊥) ⊥))) ))
             (derived-proof (inference<-metainference metaproof)))
        (and (proof? derived-proof)
             (equal? (conclusion derived-proof) '(→ p (→ (→ p ⊥) ⊥)))
             (= (length derived-proof) 35))))

;;; now we can consider some more serious (meta)proofs!

(define (metaproof-→⊥A #;for A) ;; ex falso quodlibet
  `( ((⊥ (→ ,A ⊥)) ⊢ ⊥)                     ;; hyp
     (         (⊥) ⊢ (→ (→ ,A ⊥) ⊥))        ;; DT
     (         (⊥) ⊢ (→ (→ (→ ,A ⊥) ⊥) ,A)) ;; Ax3
     (         (⊥) ⊢ ,A)                    ;; MP 3,2
     (          () ⊢ (→ ⊥ ,A)) ))           ;; DT

;;; a procedure generating metaproofs is a meta-metaproof, isn't it?
(define (proof-→⊥A #;for A) (inference<-metainference (metaproof-→⊥A A)))

(e.g. (proof? (proof-→⊥A #;for '(→ p q))))
(e.g. (length (proof-→⊥A #;for '(→ p q))) ===> 17)

;;; these we're going to use later on too:

(define (contraposition-metaproof #;for A B)
  `( (((→ ,A ,B) (→ ,B ⊥) ,A) ⊢ ,A)        ;; hyp
     (((→ ,A ,B) (→ ,B ⊥) ,A) ⊢ (→ ,A ,B)) ;; hyp
     (((→ ,A ,B) (→ ,B ⊥) ,A) ⊢ ,B)        ;; MP
     (((→ ,A ,B) (→ ,B ⊥) ,A) ⊢ (→ ,B ⊥))  ;; hyp
     (((→ ,A ,B) (→ ,B ⊥) ,A) ⊢ ⊥)         ;; MP
     (  ((→ ,A ,B) (→ ,B ⊥)) ⊢ (→ ,A ⊥))   ;; DT
     (          ((→ ,A ,B)) ⊢ (→ (→ ,B ⊥) (→ ,A ⊥))) ;; DT
     (                 () ⊢ (→ (→ ,A ,B) (→ (→ ,B ⊥) (→ ,A ⊥)))) )) ;; DT

(e.g. (metaproof? (contraposition-metaproof 'p 'q)))
(e.g. (proof? (inference<-metainference (contraposition-metaproof 'p 'q))))
(e.g. (equal? (conclusion
               (inference<-metainference (contraposition-metaproof 'p 'q)))
              '(→ (→ p q) (→ (→ q ⊥) (→ p ⊥)))))
(e.g. (tautology? '(→ (→ p q) (→ (→ q ⊥) (→ p ⊥)))))
(e.g. (length (inference<-metainference (contraposition-metaproof 'p 'q)))
      ===> 163) 

(define (eitherway-metaproof #;for A #;and B)
  `(,@(contraposition-metaproof A B) ;; cf 2 lines below.
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ (→ ,A ,B)) ;hyp
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ (→ (→ ,A ,B) (→ (→ ,B ⊥) (→ ,A ⊥)))) ;!
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ (→ (→ ,B ⊥) (→ ,A ⊥))) ;MP 1,2
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ (→ ,B ⊥)) ;hyp
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ (→ ,A ⊥)) ;MP 4,3
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ (→ (→ ,A ⊥) ,B)) ;hyp
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ ,B) ;MP 6,5
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ (→ ,B ⊥)) ;hyp
    (((→ ,A ,B) (→ (→ ,A ⊥) ,B) (→ ,B ⊥)) ⊢ ⊥) ;MP 8,7
    (        ((→ ,A ,B) (→ (→ ,A ⊥) ,B)) ⊢ (→ (→ ,B ⊥) ⊥)) ;DT
    (        ((→ ,A ,B) (→ (→ ,A ⊥) ,B)) ⊢ (→ (→ (→ ,B ⊥) ⊥) ,B)) ;Ax3
    (        ((→ ,A ,B) (→ (→ ,A ⊥) ,B)) ⊢ ,B) ;MP 11,10
    (                      ((→ ,A ,B)) ⊢ (→ (→ (→ ,A ⊥) ,B) ,B)) ;DT
    (                             () ⊢ (→ (→ ,A ,B) (→ (→ (→ ,A ⊥) ,B) ,B))) )) ;DT

(e.g. (metaproof? (eitherway-metaproof 'p 'q)))
(e.g. (proof? (inference<-metainference (eitherway-metaproof 'p 'q))))
(e.g. (equal? (conclusion
               (inference<-metainference (eitherway-metaproof 'p 'q)))
              '(→ (→ p q) (→ (→ (→ p ⊥) q) q))))
(e.g. (tautology? '(→ (→ p q) (→ (→ (→ p ⊥) q) q))))
(e.g. (length (inference<-metainference (eitherway-metaproof 'p 'q)))
      ===> 631) ; impressive, isn't it?
       

;;; there's more fun to be had in 3--generating-proofs.scm

