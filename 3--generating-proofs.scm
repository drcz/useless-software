;;; this stuff is loosely based on chapter 2 of Allan Ramsay's
;;; ``Formal Methods in Artificial Intelligence''.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(use-modules (grand scheme))
(define empty? null?)
(define ((equals? x) y) (equal? x y))

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

;;; again to keep each file self-contained we'll repeat some definitions from
;;; previous sections; however this material is a bit


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FORMULAS, AXIOMS, VALUES, TAUTOLOGIES
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

(define (tautology? formula)
  (every (lambda (valuation) (value formula valuation))
         (all-valuations #;over (names formula))))

(e.g. (tautology? '(→ p (→ q p))))
(e.g. (tautology? '(→ (→ (→ (→ p p) ⊥) ⊥) (→ p p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; INFERENCES and PROOFS, METAINFERENCES and METAPROOFS.
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
(e.g. (not (proof? '(p (→ p q) q))))


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
           (let* (((implication antecendent ) (follows-by-MP? formula previous))
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
 (relativized '( (→ p q)  ; hyp
                 p        ; hyp
                 q )      ; MP 1,2
              #;wrt '(→ p q))
 ===> ((→ (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
          (→ (→ (→ p q) (→ (→ p q) (→ p q))) (→ (→ p q) (→ p q))))
       (→ (→ p q) (→ (→ (→ p q) (→ p q)) (→ p q)))
       (→ (→ (→ p q) (→ (→ p q) (→ p q))) (→ (→ p q) (→ p q)))
       (→ (→ p q) (→ (→ p q) (→ p q)))
       (→ (→ p q) (→ p q))
       p
       (→ p (→ (→ p q) p))
       (→ (→ p q) p)
       (→ (→ (→ p q) (→ p q)) (→ (→ (→ p q) p) (→ (→ p q) q)))
       (→ (→ (→ p q) p) (→ (→ p q) q))
       (→ (→ p q) q)))
 
(e.g. (all-hypotheses (relativized '( (→ p q)  ; hyp
                                      p        ; hyp
                                      q )      ; MP 1,2
                                   #;wrt '(→ p q)))
      ===> (p))

(define (judgement? x)
  (and-let* (((hypotheses '⊢ formula) x))
    (and (every formula? hypotheses)
         (formula? formula))))

(e.g. (judgement? '(() ⊢ (→ p p))))

(define (justified? judgement)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (or (axiom? formula)
        (member? formula hypotheses))))

(e.g. (justified? '(() ⊢ (→ q (→ p q)))))
(e.g. (justified? '((q p) ⊢ (→ q (→ p q)))))
(e.g. (justified? '((q p) ⊢ p)))
(e.g. (not (justified? '((q p) ⊢ (→ p q)))))

(define (judgement<-inference inference)
  `(,(all-hypotheses inference) ⊢ ,(conclusion inference)))

(e.g. (judgement<-inference (proof-→AA 'p)) ===> (() ⊢ (→ p p)))

(e.g. (judgement<-inference '(p
                              (→ p q)
                              q)) ===> ((p (→ p q)) ⊢ q))


(define (metainference? x)
  (and (list? x)
       (not (empty? x))
       (every judgement? x)))

(e.g. (metainference? '( ((p (→ p q)) ⊢ p)
                         ((p (→ p q)) ⊢ (→ p q))
                         ((p (→ p q)) ⊢ q) )))

(define all-submetainferences all-subinferences)


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
                                `(,judgement* ,judgement** ,con*))))
                       previous-judgements))))
         previous-judgements)))

(e.g. (⊢-follows-by-MP? '((p r (→ p q)) ⊢ q)
                        '(   ((p (→ p q)) ⊢ p)
                             ((p (→ p q) r) ⊢ (→ p q))))
      ===> ( ((p (→ p q) r) ⊢ (→ p q)) ;; justifies implication
             ((p (→ p q)) ⊢ p)         ;; justifies antecentent
             q))                       ;; actual conclusion formula


(e.g. (not (⊢-follows-by-MP? '((p r (→ p q)) ⊢ q)
                             '( ((p (→ p q) r) ⊢ p)
                                ((p (→ p q)) ⊢ (→ p q))))))


(define (⊢-follows-by-subset? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ formula) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* formula)
                  (subset? hypotheses* hypotheses)
                  judgement*)))
         previous-judgements)))

(e.g. (⊢-follows-by-subset? '((p q r) ⊢ (→ p q))
                            '((   (q) ⊢ (→ p q))))
      ===> ((q) ⊢ (→ p q))) ;; easy.

(define (⊢-follows-by-composition? judgement #;from previous-judgements)
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

(e.g. (⊢-follows-by-composition? '((p q) ⊢ r)
                                 '( (            (p q) ⊢ (→ p q))
                                    (            (p q) ⊢ q)
                                    (              (p) ⊢ (→ p p))
                                    (((→ p p) (→ p q) q) ⊢ r)))
      ===> (((p) ⊢ (→ p p))   ;;; justifies first hypothesis
            ((p q) ⊢ (→ p q)) ;;; ... second ...
            ((p q) ⊢ q)       ;;; ... third ...
            (((→ p p) (→ p q) q) ⊢ r))) ;;; finally: justifies the initial frm.


(define (⊢-follows-by-DT? judgement #;from previous-judgements)
  (and-let* (((hypotheses '⊢ ('→ ant con)) judgement))
    (any (lambda (judgement*)
           (and-let* (((hypotheses* '⊢ formula*) judgement*))
             (and (equal? formula* con)
                  (member? ant hypotheses*)
                  (subset? (difference hypotheses* `(,ant)) hypotheses)
                  `(,judgement* ,ant))))
         previous-judgements)))

(e.g. (⊢-follows-by-DT? '((r) ⊢ (→ p q)) #;from '(((p) ⊢ q )))
      ===> (((p) ⊢ q) ;;; judgement used in derivation
            p))       ;;; and the hypothesis to relativize it with.

(e.g. (not (⊢-follows-by-DT? '(() ⊢ (→ p q)) #;from '(((p r) ⊢ q )))))

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


(define (sufficient? metainference) (empty? (all-assertions metainference)))

(define (metaproof? metainference)
  (and-let* (((hypotheses '⊢ formula) (conclusion metainference)))
    (and (empty? hypotheses)
         (sufficient? metainference))))

(e.g. (metaproof? '( ((p (→ p ⊥)) ⊢ p)                       ;; just. (hyp)
                     ((p (→ p ⊥)) ⊢ (→ p ⊥))                 ;; just. (hyp)
                     ((p (→ p ⊥)) ⊢ ⊥)                       ;; by MP
                     (        (p) ⊢ (→ (→ p ⊥) ⊥))           ;; by DT
                     (         () ⊢ (→ p (→ (→ p ⊥) ⊥))) ))) ;; by DT
                     
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
                             (⊢-follows-by-subset? judgement previous)))
                   (assoc-ref constructed judgement*))
                 ;;; following by composition requires concatenating all
                 ;;; inferences for hypotheses and the inference from them
                 ;;; to the formula that current judgement is about:
                 (and-let* ((judgements
                             (⊢-follows-by-composition? judgement previous)))
                   (append-map (lambda (i) (assoc-ref constructed i)) judgements))
                 ;;; following by DT requires relativizing parent judgement's
                 ;;; inference wrt to [some] hypothesis:
                 (and-let* (((judgement* hypothesis*)
                             (⊢-follows-by-DT? judgement previous))
                            (inference*
                             (assoc-ref constructed judgement*)))
                   (relativized inference* hypothesis*))
                 ;;; finally, following by MP requires inferences for implication
                 ;;; and for antecentent, followed by the conclusion alone:
                 (and-let* (((imp-judgement ant-judgement conclusion)
                             (⊢-follows-by-MP? judgement previous))
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

;;; again, after ~500 lines of mostly repeated definitions and examples,
;;; we're ready to go with some exciting stuff!


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; GENERATING PROOFS.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; based on [probably] Kalmar's proof of [definitely] completeness theorem;
;;; hold my coffee! four useful metainferences:

(define (metainference-kalmar-1 A B)
  `( ,@(metaproof-→⊥A #;for B) ;; ex falso quodlibet, cf below...
     (((→ ,A ⊥) (→ ,B ⊥) ,A) ⊢ ,A)           ;; hyp
     (((→ ,A ⊥) (→ ,B ⊥) ,A) ⊢ (→ ,A ⊥))     ;; hyp
     (((→ ,A ⊥) (→ ,B ⊥) ,A) ⊢ ⊥)            ;; MP
     (((→ ,A ⊥) (→ ,B ⊥) ,A) ⊢ (→ ⊥ ,B))     ;; see, there!
     (((→ ,A ⊥) (→ ,B ⊥) ,A) ⊢ ,B)           ;; MP 
     (   ((→ ,A ⊥) (→ ,B ⊥)) ⊢ (→ ,A ,B)) )) ;; DT 

(define (metainference-kalmar-2 A B)
  `( (((→ ,A ⊥) ,B) ⊢ ,B)               ;; hyp
     (((→ ,A ⊥) ,B) ⊢ (→ ,B (→ ,A ,B))) ;; Ax1
     (((→ ,A ⊥) ,B) ⊢ (→ ,A ,B)) ))     ;; MP

(define (metainference-kalmar-3 A B)
  `( ((,A (→ ,B ⊥) (→ ,A ,B)) ⊢ ,A)                 ;; hyp
     ((,A (→ ,B ⊥) (→ ,A ,B)) ⊢ (→ ,A ,B))          ;; hyp
     ((,A (→ ,B ⊥) (→ ,A ,B)) ⊢ ,B)                 ;; MP
     ((,A (→ ,B ⊥) (→ ,A ,B)) ⊢ (→ ,B ⊥))           ;; hyp
     ((,A (→ ,B ⊥) (→ ,A ,B)) ⊢ ⊥)                  ;; MP
     (          (,A (→ ,B ⊥)) ⊢ (→ (→ ,A ,B) ⊥)) )) ;; DT

(define (metainference-kalmar-4 A B)
  `( ((,A ,B) ⊢ ,B)           ;; hyp
     ((,A ,B) ⊢ (→ ,A ,B)) )) ;; DT

(define (metaproof-→AA #;with A)
  `( (() ⊢ (→ (→ ,A (→ (→ ,A ,A) ,A)) (→ (→ ,A (→ ,A ,A)) (→ ,A ,A))) ) ;Ax2
     (() ⊢ (→ ,A (→ (→ ,A ,A) ,A)) ) ;Ax1
     (() ⊢ (→ (→ ,A (→ ,A ,A)) (→ ,A ,A))) ;MP
     (() ⊢ (→ ,A (→ ,A ,A))) ;Ax1
     (() ⊢ (→ ,A ,A)) )) ; MP


;;; it's hard to find a nice name for the next one; Ramsay (likely following
;;; Kalmar?) uses prime symbol, but it'd be silly to call it (prime _ _)...
(define (holding formula #;in valuation)
  (if (value formula valuation) formula
      #;otherwise `(→ ,formula ⊥)))

(e.g. (holding 'p '((p . #t) (q . #f))) ===> p)
(e.g. (holding 'q '((p . #t) (q . #f))) ===> (→ q ⊥))
(e.g. (holding '(→ q p) '((p . #t) (q . #f))) ===> (→ q p))
(e.g. (holding '(→ p q) '((p . #t) (q . #f))) ===> (→ (→ p q) ⊥))
;;; got it, dude?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lm. for any valuation v and any formula φ over names (p1 ... pn)
;;; let pi' stand for (holding pi v) and φ' for (holding φ v). then
;;; we have ((p1' ... pn') ⊢ φ').

;;; Proof: it's [moderately] easy to construct such inference by induction
;;; on complexity of fomula φ:
;;; * base cases:
;;;  - when φ is a name (ie some pi) it's clear φ' is pi', which is justified;
;;;  - when φ is ⊥ obviously ⊥' = (→ ⊥ ⊥) which is a theorem (cf proof→AA);
;;; * induction step:
;;;  when φ is (→ ψ ψ*) there are 4 possibilities (one for each possible
;;;  form of ψ' and ψ*'). these are covered by inferences kalmar-1 to kalmar-4,
;;;  and the rest follows from induction hypotheses, i.e.
;;;  ((p1' ... pn') ⊢ ψ') and ((p1' ... pn') ⊢ ψ*').

(define (kalmar formula valuation)
  (let ((hypotheses (map (lambda (f) (holding f valuation)) (map car valuation)))
        (conclusion (holding formula valuation)))
     `(,@(match formula
           ('⊥
            (metaproof-→AA #;with '⊥))
           ((? name?)
            `( ((,(holding formula valuation)) ⊢ ,(holding formula valuation)) ))
           (('→ f f*)
            `(,@(kalmar f valuation)
              ,@(kalmar f* valuation)
              ,@(match `(,(value f valuation) ,(value f* valuation))
                  ((#f #f) (metainference-kalmar-1 f f*))
                  ((#f #t) (metainference-kalmar-2 f f*))
                  ((#t #f) (metainference-kalmar-3 f f*))
                  ((#t #t) (metainference-kalmar-4 f f*))))))
       (,hypotheses ⊢ ,conclusion))))


(e.g. (kalmar '(→ (→ p q) (→ p r)) '((p . #t) (q . #f) (r . #t)))
      ===> (((p) ⊢ p)
            ((p (→ q ⊥) r) ⊢ p)

            (((→ q ⊥)) ⊢ (→ q ⊥))
            ((p (→ q ⊥) r) ⊢ (→ q ⊥))

            ((p (→ q ⊥) (→ p q)) ⊢ p)
            ((p (→ q ⊥) (→ p q)) ⊢ (→ p q))
            ((p (→ q ⊥) (→ p q)) ⊢ q)
            ((p (→ q ⊥) (→ p q)) ⊢ (→ q ⊥))
            ((p (→ q ⊥) (→ p q)) ⊢ ⊥)
            ((p (→ q ⊥)) ⊢ (→ (→ p q) ⊥))
            ((p (→ q ⊥) r) ⊢ (→ (→ p q) ⊥))

            ((p) ⊢ p)
            ((p (→ q ⊥) r) ⊢ p)

            ((r) ⊢ r)
            ((p (→ q ⊥) r) ⊢ r)

            ((p r) ⊢ r)
            ((p r) ⊢ (→ p r))
            ((p (→ q ⊥) r) ⊢ (→ p r))

            (((→ (→ p q) ⊥) (→ p r)) ⊢ (→ p r))
            (((→ (→ p q) ⊥) (→ p r)) ⊢ (→ (→ p r) (→ (→ p q) (→ p r))))
            (((→ (→ p q) ⊥) (→ p r)) ⊢ (→ (→ p q) (→ p r)))
            ((p (→ q ⊥) r) ⊢ (→ (→ p q) (→ p r)))))

(e.g. (let* ((mi (kalmar '(→ (→ p q) (→ p r))
                         '((p . #t) (q . #f) (r . #t))))
             (i (inference<-metainference mi)))
        (and (metainference? mi)
             (sufficient? mi)
             (inference? i)
             (equal? (conclusion i) '(→ (→ p q) (→ p r)))
             (equal? (all-hypotheses i) '((→ q ⊥) p r))
             (= (length i) 23))))

(e.g. (let* ((mi (kalmar '(→ (→ p r) (→ r q))
                         '((p . #t) (q . #f) (r . #t))))
             (i (delete-duplicates (inference<-metainference mi)))) ;; :)
        (and (metainference? mi)
             (sufficient? mi)
             (inference? i)
             (equal? (conclusion i) '(→ (→ (→ p r) (→ r q)) ⊥))
             (subset? (all-hypotheses i) '(p (→ q ⊥) r))
             (= (length i) 34))))

(e.g. (let* ((mi (kalmar '(→ (→ p r) (→ r q))
                         '((p . #f) (q . #t) (r . #t))))
             (i (delete-duplicates (inference<-metainference mi)))) ;; :)
        (and (metainference? mi)
             (sufficient? mi)
             (inference? i)
             (equal? (conclusion i) '(→ (→ p r) (→ r q)))
             (subset? (all-hypotheses i) '((→ p ⊥) q r))
             (= (length i) 8))))



;;; m'kay now the real mindfuck! obviously we assume (tautology? formula).
;;; this is actual application of completeness theorem. although a bit awkward
;;; it's more or less proof from ch2 in Ramsay ``played in reverse'' and
;;; more explicit on the ending.
;;; we assume hypotheses were built from all-valuations, therefore
;;; they are ordered s.t. leftmost term is first #t then #f with the
;;; tail of valuation exactly the same.
;;; ...so that we can group them into pairs and use eitherway proof and MP
;;; to arrive at new list of judgements, free of hypotheses n and (→ n ⊥).

;;; another silly name:
(define (without-name n #;from judgements) ;; yields a list (!) of metainferences
  (map (lambda ((j j*))
         (let* (((h '⊢ f) j)
                ((h* '⊢ f*) j*)
                (h** (delete n h))) ;; equiv. (delete `(→ ,n ⊥))
           `( (,h** ⊢ (→ ,n ,f)) ;; DT from j
              (,h** ⊢ (→ (→ ,n ⊥) ,f)) ;; DT from j*
              (,h** ⊢ (→ (→ ,n ,f) (→ (→ (→ ,n ⊥) ,f) ,f))) ;; by eitherway
              (,h** ⊢ (→ (→ (→ ,n ⊥) ,f) ,f)) ;; MP
              (,h** ⊢ ,f) ))) ;; MP
       (chunks judgements 2)))

(e.g. (without-name 'p '(((p q) ⊢ (→ q (→ p q)))
                         (((→ p ⊥) q) ⊢ (→ q (→ p q)))
                         ((p (→ q ⊥)) ⊢ (→ q (→ p q)))
                         (((→ p ⊥) (→ q ⊥)) ⊢ (→ q (→ p q)))))
      ===> ((((q) ⊢ (→ p (→ q (→ p q)))) ;; DT
             ((q) ⊢ (→ (→ p ⊥) (→ q (→ p q)))) ;; DT
             ((q) ⊢ (→ (→ p (→ q (→ p q))) ;; eitherway
                       (→ (→ (→ p ⊥) (→ q (→ p q))) (→ q (→ p q)))))
             ((q) ⊢ (→ (→ (→ p ⊥) (→ q (→ p q))) (→ q (→ p q)))) ;; MP
             ((q) ⊢ (→ q (→ p q)))) ;; MP
            ((((→ q ⊥)) ⊢ (→ p (→ q (→ p q)))) ;; DT
             (((→ q ⊥)) ⊢ (→ (→ p ⊥) (→ q (→ p q)))) ;; DT
             (((→ q ⊥)) ⊢ (→ (→ p (→ q (→ p q))) ;; eitherway
                             (→ (→ (→ p ⊥) (→ q (→ p q))) (→ q (→ p q)))))
             (((→ q ⊥)) ⊢ (→ (→ (→ p ⊥) (→ q (→ p q))) (→ q (→ p q)))) ;; MP
             (((→ q ⊥)) ⊢ (→ q (→ p q)))))) ;; MP

;;; HEART OF IT ALL:
(define (metaproof<-tautology formula)
  (let* ((names (names formula))
         (valuations (all-valuations names))
         (kalmar-metainferences
          (map (lambda (val) (kalmar formula val)) valuations))
         (eitherway-metaproofs
          (map (lambda (name) (eitherway-metaproof name formula)) names))
         (judgements (map conclusion kalmar-metainferences)))
    (let with-names-removed ((names names)
                             (last-judgements judgements)
                             (new-judgements '()))
      (match names
        (() `(,@(apply append kalmar-metainferences)
              ,@(apply append eitherway-metaproofs)
              ,@new-judgements))
        ((name . names*)
         (let* ((metainferences (without-name name last-judgements))
                (last-judgements* (map conclusion metainferences))
                (new-judgements* (apply append metainferences)))
           (with-names-removed names*
                               last-judgements*
                               `(,@new-judgements ,@new-judgements*))))))))


(e.g. (let* ((thm '(→ p p))
             (mi (metaproof<-tautology thm))
             (i (inference<-metainference mi)))
        (and (tautology? thm)
             (metainference? mi)
             (metaproof? mi)
             (inference? i)
             (proof? i)
             (equal? (conclusion i) thm)
             (= (length i) 21))))

(e.g. (let* ((thm '(→ (→ p q) (→ (→ q ⊥) (→ p ⊥))))
             (mi (metaproof<-tautology thm))
             (i (inference<-metainference mi)))
        (and (tautology? thm)
             (metainference? mi)
             (metaproof? mi)
             (inference? i)
             (proof? i)
             (equal? (conclusion i) thm)
             (= (length i) 2790))))

;;; strange isn't it?
