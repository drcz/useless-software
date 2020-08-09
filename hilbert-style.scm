(use-modules (grand scheme))
(define empty? null?)
(define ((equals? x) y) (equal? x y))

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


;;; some shapes of formulas we claim to be AXIOMS:
(define (axiom? x)
  (match x
    (('→ A ('→ B A))
     (and (formula? A) (formula? B) 'Ax1))
    (('→ ('→ A ('→ B C)) ('→ ('→ A B) ('→ A C)))
     (and (formula? A) (formula? B) (formula? C) 'Ax2))
    (('→ ('→ ('→ A '⊥) '⊥) A)
     (and (formula? A) 'Ax3))
    (otherwise #f)))

(e.g. (axiom? '(→ p (→ (→ q ⊥) p))) ===> Ax1)
(e.g. (axiom? '(→ (→ (→ (→ q q) ⊥) ⊥) (→ q q))) ===> Ax3)
(e.g. (not (axiom? '(→ ⊥ p))))


;;; a non-empty sequence of formulas we'll call an INFERENCE:
(define (inference? x)
  (and (list? x)
       (not (empty? x))
       (every formula? x)))

(e.g. (inference? '((→ p (→ q p))
                    p
                    (→ q p)
                    (→ p q)
                    q)))


;;; the last formula we'll call a CONCLUSION:
(define (conclusion #;of inference) (last inference))


;;; some initial fragment of inference we'll call a SUBINFERENCE:
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

;;; obviously any subinference is an inference too:
(e.g. (every inference?
             (all-subinferences '( (→ p (→ q p)) p (→ q p) (→ p q) q ))))

;;; a formula in an inference is either an axiom, or follows from previous ones by
;;; MODUS PONENS rule; otherwise it's a HYPOTHESIS:
(define (follows-by-MP? formula previous-formulas)
  (any (lambda (formula*)
         (and-let* ((('→ antecendent consequent) formula*))
           (and (equal? consequent formula)
                (any (equals? antecendent) previous-formulas))))
       previous-formulas))

(e.g. (follows-by-MP? 'p '(q (→ q p))))
(e.g. (not (follows-by-MP? 'p '(r (→ q p)))))
(e.g. (not (follows-by-MP? 'p '(q r p (→ q r)))))


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

(e.g. (all-hypotheses '( (→ p q) ;; 1. Hyp
                         (→ q r) ;; 2. Hyp
                         p       ;; 3. Hyp
                         q       ;; 4. MP 3,1
                         r ))    ;; 5. MP 4,2
      ===> ( (→ p q)
             (→ q r)
             p ))

;;; an inference with no hypotheses is called a PROOF (its conclusion a THEOREM)
(define (proof? x)
  (and (inference? x)
       (empty? (all-hypotheses x))))

(e.g. (proof? '( (→ (→ p (→ (→ p p) p))
                    (→ (→ p (→ p p)) (→ p p))) ; 1. Ax2
                 (→ p (→ (→ p p) p))           ; 2. Ax1
                 (→ (→ p (→ p p)) (→ p p))     ; 3. MP 1,2
                 (→ p (→ p p))                 ; 4. Ax1
                 (→ p p) )))                   ; 5. MP 3,4


;;; the above proof will be useful later on. notice that the sentence name p
;;; can be replaced with any formula A and the proof is still valid.

(define (proof-→AA #;with A)
  `( (→ (→ ,A (→ (→ ,A ,A) ,A))
        (→ (→ ,A (→ ,A ,A)) (→ ,A ,A))) ; 1. Ax2
     (→ ,A (→ (→ ,A ,A) ,A))            ; 2. Ax1
     (→ (→ ,A (→ ,A ,A)) (→ ,A ,A))     ; 3. MP 1,2
     (→ ,A (→ ,A ,A))                   ; 4. Ax1
     (→ ,A ,A) ))                       ; 5. MP 3,4


(e.g. (proof-→AA '(→ p q))
      ===> ( (→ (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
                (→ (→ (→ p q) (→ (→ p q) (→ p q))) (→ (→ p q) (→ p q))))
             (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
             (→ (→ (→ p q) (→ (→ p q) (→ p q))) (→ (→ p q) (→ p q)))
             (→ (→ p q) (→ (→ p q) (→ p q)))
             (→ (→ p q) (→ p q)) ))

(e.g. (proof? (proof-→AA '(→ p q))))
(e.g. (conclusion (proof-→AA '(→ p q))) ===> (→ (→ p q) (→ p q)))

;;; again, obviously, all subinferences of a proof are proofs (of consecutive
;;; formulas):
(e.g. (every proof? (all-subinferences (proof-→AA '(→ p q)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; now we can make claims about existence of certain inferences.
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

;;; given we know some inferences with fixed hypotheses exist, we can infer
;;; existence of other inferences from the same (or wider) hypotheses, e.g.
;;; for some hypotheses Σ if we know (Σ ⊢ p) and (Σ ⊢ (→ p q)) we should be
;;; able to recognize that (Σ ⊢ q) -- as we could concatenate inferences for
;;; p and (→ p q) and then append q as it follows by modus ponens.

;;; also if we know (Σ ⊢ φ) then (Σ* ⊢ φ) if all hypotheses in Σ are also in Σ*
;;; (i.e. when (subset Σ Σ*) ===> #t).

;;; finally there is one very useful result called Deduction Theorem, which
;;; states that if ((φ) ⊢ φ*) then (() ⊢ (→ φ φ*)), and more generally if
;;; Σ is Σ* with φ included (or using set-theoretic metaphor Σ = Σ* ∪ {φ})
;;; then whenever (Σ ⊢ φ*) we have (Σ* ⊢ (→ φ φ*)).
;;; This theorem holds because given an inference from Σ to some φ*, we can
;;; automagically derive a new inference.

;;; first it's handy to know what justifies the use of MP anyway. it's just as
;;; checking if a formula is derivable with MP, only returning found implication
;;; and antecendent (for convenience) instead of truth-value alone (we could have
;;; done that before but let's pretend we do care about types):
(define (MP-justification #;for formula #;from previous-formulas)
  (any (lambda (formula*)
         (and-let* ((('→ antecendent consequent) formula*))
           (and (equal? consequent formula)
                (any (equals? antecendent) previous-formulas)
                `(,antecendent ,formula*))))
       previous-formulas))

(e.g. (MP-justification 'p '((→ q p) r q))
      ===> (q ;; antecentent
            (→ q p))) ;; implication
(e.g. (MP-justification '(→ p r) '((→ (→ q r) (→ p r)) r (→ q r) q))
      ===> ((→ q r) ;; antecentent
            (→ (→ q r) (→ p r)))) ;; implication

;;; ok, now we're ready to derive new inferences:
(define (dehypothesized inference #;wrt hypothesis)
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
           (let* (((antecendent implication) (MP-justification formula previous))
                  ;;; and we know we have these already dehypothesized to:
                  (antecendent* `(→ ,hypothesis ,antecendent))
                  (implication* `(→ ,hypothesis ,implication))
                  ;;; and we want:
                  (formula* `(→ ,hypothesis ,formula)))
             `( (→ ,implication* (→ ,antecendent* ,formula*)) ;; that's Ax2 (!),
                (→ ,antecendent* ,formula*)  ;; MP on implication* and one above,
                ,formula* ))))))             ;; MP on antecentent* and one above.
     (all-subinferences inference))))

(e.g.
 (dehypothesized '( (→ p (→ q p)) ;; 1. Ax1
                    p             ;; 2. Hyp
                    (→ q p)       ;; 3. MP 1,2
                    (→ p q)       ;; 4. Hyp
                    q )           ;; 5. MP 2,4
                 #;wrt 'p)
 ===> (  (→ p (→ q p))
         (→ (→ p (→ q p)) (→ p (→ p (→ q p))))
       (→ p (→ p (→ q p)))
         (→ (→ p (→ (→ p p) p)) (→ (→ p (→ p p)) (→ p p)))
         (→ p (→ (→ p p) p))
         (→ (→ p (→ p p)) (→ p p))
         (→ p (→ p p))
       (→ p p)
         (→ (→ p (→ p (→ q p))) (→ (→ p p) (→ p (→ q p))))
         (→ (→ p p) (→ p (→ q p)))
       (→ p (→ q p))
         (→ p q)
         (→ (→ p q) (→ p (→ p q)))
       (→ p (→ p q))
         (→ (→ p (→ p q)) (→ (→ p p) (→ p q)))
         (→ (→ p p) (→ p q))
       (→ p q) ))


(e.g. (all-hypotheses  (dehypothesized '( (→ p (→ q p))
                                          p
                                          (→ q p)
                                          (→ p q)
                                          q )
                                       #;wrt 'p))
      ===> ((→ p q)))

;;; we can get rid of that one too, to obtain a proof. in general we can now
;;; keep getting rid of all hypotheses from any inference, thus obtaining proofs:
(define (proof<-inference inference)
  (fold-left dehypothesized inference (all-hypotheses inference)))

(e.g.
 (let* ((inference '( (→ p (→ q p)) p (→ q p) (→ p q) q ))
        (proof (proof<-inference inference)))
   (and (equal? (all-hypotheses inference) '(p (→ p q)))
        (= (length inference) 5)
        (equal? (conclusion inference) 'q)
        (empty? (all-hypotheses proof))
        (= (length proof) 55)
        (equal? (conclusion proof) '(→ (→ p q) (→ p q))))))

;;; as you can see, proof generated this way are not the shortest ones,
;;; we know very well that the above theorem can be obtained much easier:
(e.g. (let ((other-proof (proof-→AA '(→ p q))))
        (and (empty? (all-hypotheses other-proof))
             (= (length other-proof) 5)
             (equal? (conclusion other-proof) '(→ (→ p q) (→ p q))))))
;;; but the point was to derive it from some earlier inference.

;;; Deduction Theorem is an important one in reasoning about existence of
;;; inferences without deriving them (also in speculating what would be
;;; the implications of existence of some proof), and actually the only
;;; one we needed to start working with judgements instead of actual proofs.

;;; We'll call these derivations metainferences, and will try doing
;;; things analoguosly to inferences:
(define (metainference? x)
  (and (list? x)
       (not (empty? x))
       (every judgement? x)))

(e.g. (metainference? '( ((p (→ p q)) ⊢ p)       ;; justified (hypothesis)
                         ((p (→ p q)) ⊢ (→ p q)) ;; justified (hypothesis)
                         ((p (→ p q)) ⊢ q) )))   ;; exists by MP

;;; actually we can use (conclusion _) here as well so we will refer to the last
;;; judgement of metainference as its CONCLUSION too.
;;; similarly we have submetainferences :)
(define all-submetainferences all-subinferences)

;;; we can easily figure out if existence of some inference is granted by
;;; deduction theorem:
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

;;; and similarly for modus ponens rule:
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

;;; judgements which are not justified or following by DT or MP we'll call
;;; ASSERTIONS. we could call them hypotheses too, or ⊢-hypotheses but we don't.

(define (all-assertions #;in metainference)
  (filter-map (lambda (submetainference)
                (let* (((previous ... judgement) submetainference))
                  (and (not (justified? judgement))
                       (not (⊢-follows-by-DT? judgement previous))
                       (not (⊢-follows-by-MP? judgement previous))
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

;;; a metainference with no assertions we'll call SUFFICIENT:
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
                     
;;; This is quite useful. We can actually use metaproofs instead of working with
;;; ``actual proofs'', because metainferences are as convincing as inferences,
;;; yet much shorter.
;;; that's extremely useless anyway (mind sentential calculus is decidable
;;; so for smaller amounts of sentential names truth table suffices to know if
;;; some proof exists, and for longer ones there's resolution procedure; and
;;; finally the really cool way of seeking counterexamples are tableaus). also
;;; nobody really cares about sentential calulus outside of few industrial
;;; problems reducible to SAT.

;;; so there's nothing stopping us from generating actual proofs from metaproofs!


(define (inference<-metainference metainference)
  (if (not (empty? (all-assertions metainference)))
      ;;; we can't invent what's lacking (yet):
      `(you have to provide these explicitly: ,(all-assertions metainference))
      (derived-inference (conclusion metainference) #;wrt metainference)))

;;; let's add some more information to our follows-by checkers:
(define (⊢-follows-by-DT? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ ('→ ant con)) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* con)
                  (member? ant hypotheses*)
                  (subset? (difference hypotheses* `(,ant)) hypotheses)
                  `(,ant ,judgement*))))
         previous-judgements)))

(e.g. (⊢-follows-by-DT? '((r) ⊢ (→ p q)) #;from '(((p) ⊢ q )))
      ===> (p
            ((p) ⊢ q)))


(define (⊢-follows-by-MP? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ ('→ ant* con*)) judgement*))
             (and (equal? con* formula)
                  (subset? hypotheses* hypotheses)
                  (any (lambda (judgement**)
                         (and-let* (((hypotheses** '⊢ formula**) judgement**))
                           (and (equal? formula** ant*)
                                (subset? hypotheses** hypotheses*)
                                `(,ant* ,con* ,judgement* ,judgement**))))
                       previous-judgements))))
         previous-judgements)))

(e.g. (⊢-follows-by-MP? '((p (→ p q)) ⊢ q)
                        '( ((p (→ p q)) ⊢ p)
                           ((p (→ p q)) ⊢ (→ p q))))
      ===> (p ;; antecedent
            q ;; consequent
            ((p (→ p q)) ⊢ (→ p q)) ;; implication judgement
            ((p (→ p q)) ⊢ p)))     ;; consequent judgement



(define (derived-inference judgement metainference)
  (or (and (justified? judgement)
           (let* (((hypotheses '⊢ formula) judgement))
             `(,formula)))
      (and-let* (((ant judgement*) (⊢-follows-by-DT? judgement metainference))
                 ((hypotheses* '⊢ formula*) judgement*)
                 (inference* (derived-inference judgement* metainference)))
        (dehypothesized inference* ant))
      (and-let* (((ant con judgement* judgement**)
                  (⊢-follows-by-MP? judgement metainference))
                 (inference* (derived-inference judgement* metainference))
                 (inference** (derived-inference judgement** metainference)))
        `(,@inference* ;; proves (→ ant con)
          ,@inference** ;; proves ant
          ,con)))) ;; next step follows by MP (obviously)

(e.g. (let* ((metaproof
              '( ((p (→ p ⊥)) ⊢ p)
                 ((p (→ p ⊥)) ⊢ (→ p ⊥))
                 ((p (→ p ⊥)) ⊢ ⊥)
                 (        (p) ⊢ (→ (→ p ⊥) ⊥))
                 (         () ⊢ (→ p (→ (→ p ⊥) ⊥))) ))
             (derived-proof
              (inference<-metainference metaproof)))
        (and (proof? derived-proof)
             (equal? (conclusion derived-proof) '(→ p (→ (→ p ⊥) ⊥)))             
             (= (length derived-proof) 35))))

;;; \o/

