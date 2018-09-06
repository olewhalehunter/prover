;; Logic and Relational Programming and Inferential Reasoning Tools
;;
(declaim (sb-ext:muffle-conditions cl:warning))
(declaim (optimize (debug 3)))

'(:NOTES
  declarative constraint/set/type/function generation
  ^ language semantics (Quantifiers & Connectives Refal Haskell Indigo Lisp?)
  Quantified Types en.wikibooks.org/wiki/Haskell/Existentially_quantified_types
  data graph display + filtering how to draw relations? (for example canonical))  

'(:TO-DO
  impelement resolution/unification procedure test Homer/Greek example
  Knowledge Database (similar to Prolog style)
  Formula Types - clean up code
  Canonical- Abductive Deductive Inductive Logic Programming/Formal Inferential Reasoning
  ^ rule pattern hypotheses derivation link/node solving
  ^ strategy reasoning (uknowns knowns substitution possibility)
  map out automata of (E s)/resolutuion unification steps
  
  pattern matching -> deep structural forming (like Egison? for procedural dep->conn map/ Relational constriant programming for producing functions/Transaction/Runtime Specification)
  en.wikipedia.org/wiki/Graph_theory#Subsumption_and_unification
  )

'(see RESOLUTION_UNIFICATION.LISP)
;;;;;;;;;;;;;;;;;;;

(defun subst-cons-lambda (new-lambda old-lambda cell)
  (if (and cell (listp cell))
      (if (funcall old-lambda cell)
	  (funcall new-lambda cell)
	  (cons (if (listp (car cell))
		    (subst-cons-lambda new-lambda old-lambda (car cell))
		    (if (funcall old-lambda (car cell))
			(funcall new-lambda (car cell))
			(car cell)))
		(subst-cons-lambda new-lambda old-lambda (cdr cell))))))

(defun replace-symbol-cell (cell old new)
  (subst-cons-lambda (lambda (x) new) (lambda (x) (eq x old)) cell))

(defun substitute-predicate (cell predicate replacement)
  (subst-cons-lambda (lambda (x) replacement)
		     (lambda (x) (and (consp x) (equal (first x) predicate)))
		     cell))

;;;;;;;;;;;;;;;;;;

(defparameter connectives '(∧ ∨ →))

(defparameter quantifiers '(∀ ∃))

(defparameter operators '(¬))

(defparameter logical-symbols
  `(,@connectives ,@quantifiers ,@operators))

(defparameter non-logical-symbols
  '(x y z x0 y0 z0 x1 y1 z1 x_ y_ z_))

(defparameter variable-symbols
  '(a b c d e f g h i j k l m))



(defun variable? (term)
  (member term variable-symbols))

(defun constant? (term)
  (not (variable? term)))


(defun implication-subformulas? (formula)
  "if FORMULA is an Implication, return the condition and consequence"
  (case (first formula)
    ('→ (let ((condition (second formula))
	      (consequence (third formula)))
	  `(,condition ,consequence)))))

(defun universal-quantified? (formula)
  "if FORMULA is Universally Quantified at its root, return the Quantified Domain and the stated Property "
  (case (first formula)
    ('∀ (let ((domain (second formula))
	      (property (third formula)))
	  `(,domain ,property)))))     
		

(defun convert-to-cnf (formula)
  "convert a quantified First Order Logic clause to Conjunctive Normal Form"
  (case (first formula)
    ('∀ (let ((domain (second formula))
	      (property (third formula)))
	  (case (first property)
	    ('→ (let ((condition (second property))
		      (consequence (third property)))
		  `(∨ (¬ ,condition) ,consequence)
		  )))		      
	  ))
    ('∃ 'make-skolem-functions)
    (otherwise formula)
    ;; Additional Steps
    ;; https://en.wikipedia.org/wiki/Conjunctive_normal_form#Converting_from_first-order_logic
    ;; ^ (convert-to-negation-normal-form)
    ;; (de-morgans-law)
    ;; (Skolemize)
    ))


(defun predicate-functionp (literal)
  "any (P X ...)"
  (if (negative-literalp literal)
      (setq literal (second literal)))
  (if (and (listp literal)
	   (symbolp (first literal))
	   (rest literal)
	   (not (member (first literal) logical-symbols)) )
      (first literal) nil))

(defun predicate-args (literal)
  "(P x y z) -> (x y z)"
  (if (negative-literalp literal)
      (setq literal (second literal)))
  (rest literal))

(defun negation (literal)
  "P -> ¬P"
  (if (and (consp literal) (negative-literalp literal))
      (second literal)
      `(¬ ,literal)))



(defun literalp (formula)
  "(¬ (P X)) or (P X)"
  (and (listp formula)
       (or (and (eq (first formula) '¬) (predicate-functionp (second formula)))
	   (predicate-functionp formula))))

(defun negative-literalp (literal)
  "(¬ (P X))"
  (and (consp literal) (eq (first literal) '¬)))

(defun clausep (formula)
  "any (∨ literal1 literal2...)"
  (and (listp formula) (eq (first formula) '∨)))
  

(defun clause-literals (clause)
  "return positive and negative literals of CLAUSE"
  (if (literalp clause)
      (list clause)
      (loop for i in clause
	 if (literalp i) collect i
	 if (clausep i) append (clause-literals i))))

(defun predicate-pattern (literal)
  "(P foo bar foo...) -> (P a b a...)"
  (setq argument-pattern (loop :for i :upto (1- (length (predicate-args literal)))
			    :collect (nth i variable-symbols)))
  (if (negative-literalp literal)
      `(¬ (,(predicate-functionp literal) ,@argument-pattern))
      `(,(predicate-functionp literal) ,@argument-pattern)))

(defun two-matching-clauses? (a b)
  "Find the same predicate in two CLAUSEs A and B where it is negated in one but not the other"
  (setq literals-a (clause-literals a)
	literals-b (clause-literals b)
	positive-a '() negated-a '()
	positive-b '() negated-b '()
	positive-in-a-negated-in-b '()
	negated-in-a-positive-in-b '()	
	)	

  (loop for literal in literals-a
     do (if (negative-literalp literal)
	    (push (list (predicate-pattern literal) literal)
		  negated-a)
	    (push (list (predicate-pattern literal) literal)
		  positive-a)))
  
  (loop for literal in literals-b
     do (if (negative-literalp literal)
	    (push (list (predicate-pattern literal) literal)
		  negated-b)
	    (push (list (predicate-pattern literal) literal)
		  positive-b)))	
  
  (loop for positive-literal in positive-a do
       (if (assoc (negation (first positive-literal)) negated-b :test #'equal)
	   (push positive-literal positive-in-a-negated-in-b)))
  (loop for positive-literal in positive-b do
       (if (assoc (negation (first positive-literal)) negated-a :test #'equal)
	   (push positive-literal negated-in-a-positive-in-b)))
  (list positive-in-a-negated-in-b
	negated-in-a-positive-in-b)
       )
  

(defun equation? (formula)
  "if FORMULA is an Equation of the form (= A B), return (A B)"
  (if (and (listp formula)
	   (eq (first formula) '=))
      (list (second formula)
	    (third formula))))


(defun equality-predicate-match? (equation)
  "if EQUATION matches F(t_1...t_i) = F(t'_1...t'_i) return (t_1...) = (t'_1...)"
  (destructuring-bind (left right)
      (equation? equation)
    (if (and (predicate-functionp left)
	     (predicate-functionp right)
	     (equal (predicate-pattern left)
		    (predicate-pattern right)))
	(list (predicate-args left)
	      (predicate-args right)))))


(defun unification (equations substitutions step &optional debug)
  "find the SUBSTITUTIONS of the Most General Unifier if it exists for EQUATIONS"
  
  (loop for equation in equations do
       (if debug
	   (print `(:EQUATIONS ,equations :SUBSTITUTIONS ,substitutions)))
     ;; Look for equation matching form F(t_1...t_i) = F(t'_1...t'_i)
       (let ((matched-predicate-args (equality-predicate-match? equation)))
	 (if matched-predicate-args
	     (destructuring-bind (left-args right-args)
		 matched-predicate-args
	       ;; remove the F(t...) = F(t'...) equation
	       (setq equations (remove equation equations :test #'equal))
	       ;; and add a new derived t... = t'... equations
	       (loop :for i :upto (1- (length left-args)) do
		  (push `(= ,(nth i left-args) ,(nth i right-args)) equations))
	       )
	     (progn
	       ;; Remove redundant equations of form 'x = x'
	       (if (equal (second equation) (third equation))
		   (setq equations (remove equation equations :test #'equal))
		   (progn
		     
		     ;; Check if equation is of form x = t where x is a variable and t a constant?
		     (let ((term-variable (equality-term-variable-match? equation)))
		       (if term-variable		       
			   (destructuring-bind (left right)
			       term-variable		     
			     ;; Occurs Check :
			     ;; if t is a term in which x occurs, the algorithm halts with no output unifier

			     ;; Substitution
			     ;; If x does not occur in t, then let [x/t] denote the substitution that maps x to t and set EQUATIONS to be the set of equations such that for each EQUATION is EQUATION[x/t] (replace all instances of x with t) and add to SUBSTITUTIONS '(X T)
			     (setq left_ left
				   right_ right)
			     (setq equations
				   (mapcar (lambda (e) (replace-symbol-cell e left right))
					   equations))		     
			     (push (list left right) substitutions)
			     ;;	       (break)
			     )))       
		     ))))))
  
  ;; if Equations are exhausted, return the substitute or nil (the identity operator)
  (if equations
      (unification equations substitutions (1+ step) debug)
      (list equations substitutions :steps step))
  )


(defun equality-term-variable-match? (equation)
  "if EQUATION is of form X = T where X is a Variable and T is a Constant Term, return (X T)"
  (destructuring-bind (left right)
      (equation? equation)
    (if (and (variable? left)
	     (constant? right))
	`(,left ,right))))
  

(defun resolution (premises)
  "perform resolution procedure on PREMISES to derive provable Conclusions"
  (let* ((conj-normal-forms
	  (loop :for formula :in premises :collect (convert-to-cnf formula))) )
    
    (destructuring-bind
	  (negated-in-b negated-in-a)
        (two-matching-clauses? (first conj-normal-forms)
			       (second conj-normal-forms))      
      (let* ((predicate-negated (second (first negated-in-a)))
	     (predicate-pattern (first (first negated-in-a))))
		
	(setq unification (unification `((= ,predicate-pattern ,predicate-negated)) '() 0 'debug)
	      most-general-unifier (first (second unification)))
	(print `(MOST GENERAL UNIFIER FOUND TO BE ,most-general-unifier))
	(destructuring-bind
	      (to-substitute substitution)
	    most-general-unifier
	  (setq to-subs to-substitute
		sub substitution
		solved-premise
		(subst-cons-lambda 
		 (lambda (x) nil)
		 (lambda (x) (and (consp x)
				  (eq (predicate-functionp x)
				      (predicate-functionp (predicate-pattern predicate-pattern)))))
		 (rest (first conj-normal-forms))))	  
	  (second (subst-cons-lambda (lambda (y) substitution)
			     (lambda (y) (eq y to-substitute))
			     solved-premise))
	  )
	))))


;;
(defparameter test-premises
      '((∀ a (→ (Greek a) (European a)))
	(Greek Homer)
	))


(defun tests ()
  (resolution test-premises)
  (unification '((= (F a) (F homer))) '() 0)

  (convert-to-cnf
   '(∀ a (→ (Greek a) (European a))))

  )

