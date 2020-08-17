;;; this stuff is loosely based on chapter 2 of Allan Ramsay's
;;; ``Formal Methods in Artificial Intelligence''.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(use-modules (grand scheme))
(define empty? null?)
(define ((equals? x) y) (equal? x y))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FORMULAS and AXIOMS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; we consider very restricted formulas
;;; [cf (expressed-as-⊥→ _) in 0--formulas-n-valuations.scm]
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

;;; following Ramsay (who seems to follow Church) we claim some (three)
;;; ``shapes'' of formulas to be AXIOMS; i.e. any formula obtained by
;;; substituting arbitrary formulas for A,B,C below is an axiom.
;;; [cf (substitute _ #;for _ #;in _) in 0--formulas-n-valuations.scm]
(define (axiom? x)
  (match x
    (('→ A ('→ B A)) ;;; Ax1
     (and (formula? A) (formula? B)))
    (('→ ('→ A ('→ B C)) ('→ ('→ A B) ('→ A C))) ;; Ax2
     (and (formula? A) (formula? B) (formula? C)))
    (('→ ('→ ('→ A '⊥) '⊥) A) ;; Ax3
     (and (formula? A)))
    (otherwise #f)))

(e.g. (axiom? '(→ p (→ (→ q ⊥) p)))) ;; Ax1 with p for A and q for B
(e.g. (axiom? '(→ (→ (→ (→ q q) ⊥) ⊥) (→ q q)))) ;; Ax3 with (→ q q) for A.
(e.g. (not (axiom? '(→ ⊥ p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; INFERENCES and PROOFS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;; the last formula of an inference we'll call its CONCLUSION:
(define (conclusion #;of inference) (last inference))

;;; and some initial fragment of inference we'll call a SUBINFERENCE:
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


;;; a formula in an inference is either an axiom, or follows from previous
;;; ones by modus ponens rule (MP); otherwise it's a HYPOTHESIS:
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

;;; an inference with no hypotheses we'll call a PROOF (its conclusion a THEOREM)
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

;;; nb we're lazy with unquotes; we could have used (substitute _ _ _) from
;;; 0--formulas-n-valuations.scm but it's just as good...

(e.g. (proof-→AA '(→ p q))
      ===> ( (→ (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
                (→ (→ (→ p q) (→ (→ p q) (→ p q))) (→ (→ p q) (→ p q))))
             (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
             (→ (→ (→ p q) (→ (→ p q) (→ p q))) (→ (→ p q) (→ p q)))
             (→ (→ p q) (→ (→ p q) (→ p q)))
             (→ (→ p q) (→ p q)) ))

(e.g. (proof? (proof-→AA '(→ p q))))
(e.g. (conclusion (proof-→AA '(→ p q))) ===> (→ (→ p q) (→ p q)))


;;; obviously (?) all subinferences of a proof are proofs:
(e.g. (every proof? (all-subinferences (proof-→AA '(→ p q)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; some operations on proofs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; TODO: concatenation? [rather pointless, no?]

;;; TODO: composition? [maybe later? maybe in 2?]
;;;;; something Ramsay doesn't state but uses implicitly is the following
;;;;; observation: if we have established that ((φ_1 ... φ_n) ⊢ φ)
;;;;; and (Σ ⊢ φ_1) ... (Σ ⊢ φ_n) for some fixed Σ and all the φ_i,
;;;;; then (Σ ⊢ φ). We can concatenate all the proofs existing by (Σ ⊢ φ_i)
;;;;; which depends only on hypotheses from Σ, and then concatenate the proof
;;;;; granted by ((φ_1 ... φ_n) ⊢ φ) because all the φ_i were already proven,
;;;;; so the proof-check would find them in the earlier parts of the proof
;;;;; (and thus no longer count φ_i as hypotheses).


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; RELATIVIZATION:

;;; when we have some inference, we can relativize it with some formula φ,
;;; i.e. turn all its formulas Ψ into implications (→ φ Ψ).
;;; such a proof, once φ is assumed or proven, can be reversed to its original
;;; form using modus ponens, so in a way this is the inverse of MP...
;;; [this will be useful for deduction theorem in 2--hilbert-metaproofs.scm]

;;; we'll modify follows-by-MP? so that it provides the implication
;;; and antecendent if it found any...
(define (follows-by-MP*? formula previous-formulas)
  (any (lambda (formula*)
         (and-let* ((('→ antecendent consequent) formula*))
           (and (equal? consequent formula)
                (any (equals? antecendent) previous-formulas)
                `(,formula* ,antecendent))))
       previous-formulas))

(e.g. (follows-by-MP*? 'p '(q (→ q p))) ===> ((→ q p) q))
(e.g. (not (follows-by-MP*? 'p '(r (→ q p)))))


;;; this is basically Ramsay's proof of deduction theorem ``played in reverse'':

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
           (let* (((implication antecendent ) (follows-by-MP*? formula previous))
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
      ===> (p)) ;; so now only hypothesis (i) is left...

;;; we can get rid of that one too, to obtain a proof. of course
;;; the original conclusion was q, while our THEOREM will be
;;; (→ p (→ (→ p q) q)).

(e.g. (let* ((initial-infenrence '( (→ p (→ q p))
                                    p
                                    (→ q p)
                                    (→ p q)
                                    q ))
             (derived-infenrece (relativized initial-infenrence
                                             #;wrt '(→ p q)))
             (derived-proof (relativized derived-infenrece #;wrt 'p)))
        (and (proof? derived-proof)
             (equal? (conclusion derived-proof)
                     '(→ p (→ (→ p q) q))))))

;;; in general we can always keep getting rid of all hypotheses from
;;; any inference, thus obtaining proofs:
(define (proof<-inference inference)
  (fold-left relativized inference (all-hypotheses inference)))

;;; mind in this one the order of hypotheses is swapped, as that's how
;;; we enlist them (in the order of appearance):
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SIMPLIFICATION.

;;; we didn't think this throught much but some obvious things can be done
;;; to inferences, especially when they are generated... we surely can:
;;; (1) get rid of all repeated formulas (the first appearance suffices)
;;; (2) get rid of all unnecessary MP dependencies (especially if the conclusion
;;; turns out to be an axiom).
;;; (3) we _might_ want to use some pre-rolled proofs/inferences like proof-→AA.
;;; (4) in the best possible case of all the MP dependencies we'd only pick
;;; the ones with shortest dependencies...

;;; below we only attempt (1) and (2):
(define (deduplicated inference) (delete-duplicates inference)) ;; dadaaam!

;;; for (2) we need to figure out which formulas are actually used in deriving
;;; the conclusion. so we must move upwards and keep noting all the formulas
;;; we used. therefore we introduce one ugly technicality: given some formula F
;;;  and an infenrece I, we'd like to get only the subinference of I above F;
;;; this way we can keep track of subinferences where the justifications of
;;; dependencies (implications and antecendents) can appear.

;;; NB we assert (member? formula inference)!
(define (subinference-above formula #;from inference)
  (let* (((formula* . inference*) inference))
    (if (equal? formula* formula) '()
        #; else `(,formula* . ,(subinference-above formula inference*)))))

;;; examples should make this clear:
(e.g. (subinference-above 'q '((→ p q) p q (→ q p) (→ p p) r))
      ===> ((→ p q) p))
(e.g. (subinference-above '(→ p p) '((→ p q) p q (→ q p) (→ p p) r))
      ===> ((→ p q) p q (→ q p)))


;;; now we can easily list all the formulas used to justify given one:
(define (used-to-justify formula #;among subinference)
  (or (and (axiom? formula)  ;; axioms are self-justified
           '())
      (and-let* (((imp ant) (follows-by-MP*? formula subinference)))
        (union `(,imp ,ant)
               (used-to-justify imp (subinference-above imp subinference))
               (used-to-justify ant (subinference-above ant subinference))))
      '())) ;;; otherwise it's some hypothesis...

(e.g. (used-to-justify 'q '((→ p q) p q))
      ===> ((→ p q)
            p))

(e.g. (used-to-justify 'r '((→ p (→ q r)) q p (→ q q) (→ q r)))
      ===> (p
            (→ p (→ q r))
            (→ q r)
            q))

(e.g. (used-to-justify '(→ q q) '((→ p (→ q r)) q p (→ q q) (→ q r)))
      ===> ()) ;; a hypothesis!
(e.g. (all-hypotheses '((→ p (→ q r)) q p (→ q q) (→ q r)))
      ===> ((→ p (→ q r)) q p #;see? (→ q q)))

;;; it doesn't seek for justification of axioms:
(e.g. (axiom? '(→ p (→ q p))))
(e.g. (used-to-justify '(→ p (→ q p)) '((→ r (→ p (→ q p))) r (→ p (→ q p))))
      ===> ()) ;;; \o/


;;; good! so now we can easily filter out only the relevant formulas...
(define (simplified inference)
  (let* ((inference* (deduplicated inference))
         (conclusion (conclusion inference)) ;; NB inference, not inference*
         (useful-formulas `(,conclusion .
                            ,(used-to-justify conclusion inference*))))
    (filter (lambda (f) (member? f useful-formulas)) inference*)))


(e.g. (simplified '((→ p (→ q r))
                    q
                    p
                    (→ q q)
                    (→ q r)))
      ===> ((→ p (→ q r))
            p
            (→ q r)))

(e.g. (simplified '((→ r (→ p (→ q p)))
                    r
                    (→ p (→ q p))))
      ===> ((→ p (→ q p))))

;;; NB if you want to preserve hypotheses you have to do it explicitly, e.g.
;;; useful-formulas `(,conclusion @,(all-hypotheses inference) . ,(used-to...
;;; -- but why would you want that?


;;; THE END.
