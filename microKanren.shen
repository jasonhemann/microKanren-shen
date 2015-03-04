\\ microKanren.shen 
\\ Jason Hemann and Dan Friedman

\* 
* Shen doesn't have Scheme's truthiness, so instead in walk and ==, we
  ask (cons? <var>) or (not (= false <var>)) in the question of an if.
* We couldn't see how to write thunks, so we use freeze and thaw. 
* We couldn't find frozen?, closure? or procedure?, so we re-ordered
  cases lines in sappend and sappend-map.
* We had to call 'unify' 'unifyy' to avoid colliding with the primitive.
* We also didn't port the relational numbers suite; that wants doing.
*\
 
(defun var (N) N)
(defun var? (X) (number? X))

(var 4)
(var? (var 4))

(defun ext-s (X V S) [[X | V] | S])
(ext-s 3 4 (ext-s 2 3 []))

(defun assv (X S)
  (if (= [] S)
    false
    (let A (head S) 
      (if (= (head A) X) A (assv X (tail S))))))

(assv cat [[horse | turtle] [cat | dog]])

(defun walk (U S) 
  (let PR (if (var? U) (assv U S) false)
    (if (cons? PR) (walk (tail PR) S) U)))

(walk 2 (ext-s 3 4 (ext-s 2 3 [])))

(defun unifyy (U V S)
  (let U (walk U S)
    (let V (walk V S)
      (cases
        (= U V) S
        (var? U) (ext-s U V S)
        (var? V) (ext-s V U S)
	(and (cons? U) (cons? V)) (let S1 (unifyy (head U) (head V) S)
	     	       	      	    (if (not (= S1 false)) (unifyy (tail U) (tail V) S1) false))
        true false))))

(unifyy [cat | 0] [1 | horse] [])

(defun == (U V)
  (lambda S/C
    (let S (unifyy U V (head S/C))
      (if (not (= S false)) [[S | (tail S/C)]] []))))

(defun call/empty-state (G) (G [[] | 0]))
       
(call/empty-state (== [cat | horse] [cat | horse]))

(defun call/fresh (F)
  (lambda S/C
    (let C (tail S/C)
      ((F (var C)) [(head S/C) | (+ 1 C)]))))

(call/empty-state 
  (call/fresh 
    (lambda X 
      (call/fresh
        (lambda Y
 	  (lambda S/C
            ((== X cat) S/C)))))))

(call/empty-state 
  (call/fresh 
    (lambda X 
      (call/fresh
        (lambda Y
 	  (lambda S/C
            ((== [cat | X] [Y | dog]) S/C)))))))

(defun disj (G1 G2) (lambda S/C (sappend (G1 S/C) (G2 S/C))))

(defun sappend (S1 S2) 
  (cases
    (= S1 []) S2
    (cons? S1) [(head S1) | (sappend (tail S1) S2)]
    true (freeze (sappend S2 (thaw S1)))))

(freeze (sappend (thaw S1) S2))

(call/empty-state
  (call/fresh 
    (lambda X
      (call/fresh
        (lambda Y
          (disj (== [X | cat] [dog | Y]) (== [X | horse] [turtle | Y])))))))

(defun conj (G1 G2) (lambda S/C (sappend-map G2 (G1 S/C))))

(defun sappend-map (G S)
  (cases
    (= S []) []
    (cons? S) (sappend (G (head S)) (sappend-map G (tail S)))
    true (freeze (sappend-map G (thaw S)))))

(call/empty-state
  (call/fresh 
    (lambda X
      (call/fresh
        (lambda Y
          (conj (== X cat) (== Y dog)))))))	

(defun hot-dogs (MEAL)
  (disj
    (== dog MEAL)
    (call/fresh 
      (lambda RES
        (conj
	  (== [hot | RES] MEAL)
	  (lambda S/C
	    (freeze ((hot-dogs RES) S/C))))))))

(call/empty-state
  (call/fresh hot-dogs))

(thaw 
  (tail 
    (call/empty-state 
      (call/fresh hot-dogs))))

(thaw 
  (tail 
    (thaw 
      (tail 
        (call/empty-state 
	  (call/fresh hot-dogs)))))) 

(defun appendo (L S O)
  (disj
    (conj (== L []) (== S O))
    (call/fresh
      (lambda A
        (call/fresh
	  (lambda D
	    (conj
	      (== [A | D] L)
	      (call/fresh
	        (lambda RES
		  (conj
		    (== [A | RES] O)
		    (lambda S/C
		      (freeze ((appendo D S RES) S/C)))))))))))))

(thaw 
  (call/empty-state 
    (call/fresh 
      (lambda Q
        (appendo [a] [] Q)))))

(defun pull (S)
  (if (or (= S []) (cons? S)) S (pull (thaw S))))

(pull 
  (call/empty-state
    (call/fresh
      (lambda Q
        (appendo Q [d e f] [c a t])))))

(pull 
  (call/empty-state
    (call/fresh
      (lambda Q
        (appendo [d e f] Q [c a t])))))

(defun take (N S)  
  (if (= 0 N)
      []
      (let S (pull S)
        (if (= S []) 
	  []
	  [(head S) | (take (- N 1) (tail S))]))))

(take 3 (call/empty-state
          (call/fresh
	    (lambda Q 
	      (call/fresh
	        (lambda O
		  (appendo Q [D E F] O)))))))

(defun walk* (U S)
  (let U (walk U S)
    (cases
      (var? U) U
      (cons? U) [(walk* (head U) S) | (walk* (tail U) S)]
      true U)))

(defun rename-S (V S)
  (let V (walk V S)
    (cases
      (var? V) (let V1 (rename-V S)
                 [[V | V1] | S])
      (cons? V) (rename-S (tail V) (rename-S (head V) S))
      true S)))

(defun rename-V (S)
  (concat _. (length S)))

(defun reify-var0 (S/C)
  (let V (walk* (var 0) (head S/C))
    (walk* V (rename-S V []))))

(defun mK-reify (L)
  (map reify-var0 L))

(mK-reify 
  (take 3 (call/empty-state
            (call/fresh
	      (lambda Q 
 	        (call/fresh
	          (lambda O
		    (appendo Q [D E F] O))))))))

\* Macros adopted from the recent extempore port, and from @deech's
vending machine thingy, and from vasil-sd on github's macros.shen *\
                             

(defun bug (MSG X)
  ((lambda Y X)
   (print (cn MSG (make-string " ~A" X)))))
     
(defun appendo (L S O)
  (conde
    ((== L []) (== S O))
    ((fresh (A D)
       (== [A | D] L)
       (fresh (RES)
         (== [A | RES] O)
	 (appendo D S RES))))))

(run 3 (Q) (fresh (L OUT) (== Q [L OUT]) (appendo L [d e f] OUT)))

(defun call/project (X F)
  (lambda S/C
    ((F (walk* X (head S/C))) S/C)))

(defun ifte (G0 G1 G2)
  (lambda S/C
    (ifte-help S/C (G0 S/C) G1 G2)))
    
(defun ifte-help (S/C S G1 G2)
  (cases
    (= S []) (G2 S/C)
    (cons? S) (sappend-map G1 S/C)
    true (freeze (ifte-help S/C (thaw S) G1 G2))))
    
(defun once (G0)
  (lambda S/C
    (once-help (G0 S/C))))
    
(defun once-help (S)
  (cases
    (= S []) []
    (cons? S) [(head S)]
    true (freeze (once-help (thaw S)))))
    
(run 3 (Q) (fresh (L O) (== Q [L O]) (once (appendo L [d e f] O))))

\\ Still need to do impure macros 
