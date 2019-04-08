;; ========================================
;;  CMPU-365, Spring 2019
;;  Monte Carlo Tree Search -- TEMPLATE!
;; ========================================

;;  Contracts for the following functions used by MCTS algorithm
;; ----------------------------------------------------------
;;     GET-ROOT-NODE
;;     NEW-MC-TREE
;;     INSERT-NEW-NODE
;;     SIM-TREE
;;     SIM-DEFAULT (defined for you) 
;;     BACKUP
;;     UCT-SEARCH
;;     SELECT-MOVE

;;  In addition, for testing, the COMPETE function is defined for you.


;;  Your MCTS functions may call the following DOMAIN-DEPENDENT
;;  functions that are defined in "othello-starter.lisp":
;; ------------------------------------------------------------------
;;     COPY-GAME               -- creates a copy of the given othello game board
;;     MAKE-HASH-KEY-FROM-GAME -- returns list of the form (WHITE-PCS BLACK-PCS WHOSE-TURN)
;;     WHOSE-TURN              -- returns *BLACK* or *WHITE*

;;  Your MCTS functions may call the following DOMAIN-DEPENDENT
;;  functions that are defined in "othello-the-rest.lisp":
;; ------------------------------------------------------------------ 
;;     DO-MOVE!        --  does a move (destructively modifies game struct)
;;     LEGAL-MOVES     --  returns VECTOR of legal moves
;;     GAME-OVER?      --  returns T or NIL
;;     DEFAULT-POLICY  --  returns random legal move

;;  Your MCTS functions should not need to call any of the MACROs defined
;;  in "othello-macros.lisp".


;;  Note:  If a player has no legal moves, but the game isn't over, then that
;;         player *must* pass...


;;  MC-NODE struct -- a node in the MCTS tree
;; ----------------------------------------------------------------------------
;;  KEY:          a hash-table key (compact rep'n of current state of game)
;;  WHOSE-TURN:   *BLACK* or *WHITE*
;;  NUM-VISITS:   the number of times this state has been visited
;;  VECK-MOVES:   a VECTOR of the legal moves from this state
;;  VECK-VISITS:  a VECTOR recording the number of times each legal move
;;                   has been visited during MCTS
;;  VECK-SCORES:  a VECTOR recording the average scores for the legal
;;                   moves visited during MCTS

(defstruct mc-node
  key             
  whose-turn      
  (num-visits 0)  
  veck-moves      
  veck-visits     
  veck-scores    
  )

;;  MC-TREE struct -- the MCTS tree
;; -------------------------------------------------------------
;;  HASHY:     a hash-table whose entries are (key,value), where
;;               key = compact repn of state, value = mc-node
veck-moves ;;  ROOT-KEY:  the hash-table key for the root node of the mcts tree

(defstruct mc-tree
  (hashy (make-hash-table :test #'equal))      
  root-key)

;;  GET-ROOT-NODE
;; ------------------------------------------------------
;;  INPUT:   TREE, a MCTS struct
;;  OUTPUT:  The MC-NODE corresponding to the root of the TREE

(defun get-root-node
    (tree)
  (gethash (mc-tree-root-key tree) (mc-tree-hashy tree)))

;; -------------------------------------------------
;;  Easiest to define the following functions
;;  in the following order (to facilitate testing)
;; -------------------------------------------------

;;  NEW-MC-TREE
;; ---------------------------------
;;  INPUT:   GAME, a game struct
;;  OUTPUT:  A new MC tree whose root state is derived
;;           from GAME.

(defun new-mc-tree
    (game)
  (let
      ((root-key (make-hash-key-from-game game)))
    (make-mc-tree :root-key root-key)))

;;  INSERT-NEW-NODE
;; -----------------------------------------
;;  INPUTS:  GAME, a game struct
;;           TREE, an MC-TREE struct
;;           KEY, a hash-key representing the state of the game
;;  OUTPUT:  The newly created and inserted node
;;  SIDE EFFECT:  Inserts a new node into TREE using KEY.

(defun insert-new-node
    (game tree key)
  (let
      ((hashy (mc-tree-hashy tree))
       (nodey (make-mc-node
	       :key key
	       :whose-turn (othello-whose-turn game)
	       :veck-moves (legal-moves game)
	       :veck-visits (make-array (length (legal-moves game)) :initial-element 0)
	       :veck-scores (make-array (length (legal-moves game)) :initial-element 0))))
    (setf (gethash key hashy) nodey)
    nodey))
       
	       

;;  SELECT-MOVE
;; ------------------------------------------
;;  INPUTS:  NODEY, an MC-NODE struct
;;           C, exploitation-exploration constant
;;  OUTPUT:  The INDEX of the selected move into the moves vector

(defun select-move
    (nodey c)
  (let* ((legal (mc-node-veck-moves nodey))
	 (scores (mc-node-veck-scores nodey))
	 (visits (mc-node-veck-visits nodey))
	 (num-visits (mc-node-num-visits nodey))
	 (turn (mc-node-whose-turn nodey))
	 (index nil))
    (cond 
     ((= turn *BLACK*)
      (dotimes (i (- (length legal) 1))
      	(cond ((= 0 (length scores))
	       (return-from select-move i)))
	(let* ((score (svref scores i))
	       (visit (svref visits i))
	       (best-val most-negative-fixnum)
	       (cur-score 0))
	  (if (= num-visits 0)
	      (return-from select-move i))
	  (setf cur-score (+ score 
			     (* c 
				(sqrt 
				 (/ (log num-visits) visit)))))
	  (cond
	   ((> cur-score best-val)
	    (setf best-val cur-score)
	    (setf index i)))))) 
     (t
      (dotimes (i (- (length legal) 1))
	(cond ((= 0 (length scores))
	       (return-from select-move i)))
	(let* ((score (svref scores i))
	       (visit (svref visits i))
	       (best-val most-positive-fixnum)
	       (cur-score 0))
	  (if (= num-visits 0)
	      (return-from select-move i))
	  (setf cur-score (- score
			     (* c
				(sqrt
				 (/ (log num-visits) visit)))))
	  (cond 
	   ((< cur-score best-val)
	    (setf best-val cur-score)
	    (setf index i)))))))
    index))
	      
	
	
;;  SIM-TREE
;; --------------------------------------
;;  INPUTS:  GAME, a game struct
;;           TREE, an MC-TREE struct
;;           C, the exploration/exploitation constant
;;  OUTPUT:  A list of the form (state0 move0 state1 move1 ... statek movek)
;;    where each state_i is a key into the hashtable, and each move_i
;;    is an index into the MOVES vector of the node assoc with state_i.

(defun sim-tree
    (game tree c)
  (let*
      ((listy nil))
    (while (not (game-over? game))
      (let*
	  ((key (make-hash-key-from-game game))
	   (node (gethash key (mc-tree-hashy tree)))
	   (new-node nil)
	   (index nil))
	(cond
	 ((null node)
	  (setf new-node (insert-new-node game tree key))
	  (setf index (select-move new-node c))
	 ; (apply #'do-move! game nil (svref (mc-node-veck-moves new-node) index)) 
	  (setf listy (cons index (cons key listy)))
	  (return-from sim-tree (reverse listy))))
	(setf index (select-move node c))
	(apply #'do-move! game nil (svref (mc-node-veck-moves node) index))
	(setf listy (cons index (cons key listy)))))
    (reverse listy)))

  

;;  SIM-DEFAULT -- defined for you!
;; ----------------------------------------------
;;  INPUT:   GAME, a game struct
;;  OUTPUT:  The result of following the game's default policy
;;             (domain-dependent method)

(defun sim-default
    (game)
  (default-policy game))

;;  BACKUP
;; ---------------------------------------------------
;;  INPUTS:  HASHY, the hash-table for the MCTS
;;           KEY-MOVE-ACC, the accumulated list of KEYs and MOVEs
;;              from a simulation run
;;           RESULT, the result (from black's perspective) of the 
;;              recently played out simulation
;;  OUTPUT:  doesn't matter
;;  SIDE EFFECT:  Updates the relevant nodes in the MC-TREE/HASHY


(defun backup
    (hashy key-move-acc result)
  (cond
   ((null key-move-acc) nil)
   (t
    (let*
	((index (first key-move-acc))
	 (node (gethash index hashy))
	 (num-visits (mc-node-num-visits node))
	 (visits (mc-node-veck-visits node))
	 (scores (mc-node-veck-scores node)))
      (svref visits (second key-move-acc))
      (setf num-visits (+ num-visits 1))
      (setf (svref visits (second key-move-acc)) 
	(+ (svref visits (second key-move-acc)) 1))
      (setf (svref scores (second key-move-acc)) 
	(+ (/ (- result (svref scores (second key-move-acc))) 
	      (svref visits (second key-move-acc)))
	   (svref scores (second key-move-acc)))))
      (backup hashy (rest (rest key-move-acc)) result))))
    
      
		    

;;  UCT-SEARCH
;; ---------------------------------
;;  INPUTS:  ORIG-GAME, a game struct
;;           NUM-SIMS, a positive integer
;;           C, the exploration/exploitation parameter
;;  OUTPUT:  Best move from that state determined by
;;             doing *NUM-SIMS* simulations of MCTS.

;;  The following global parameter can be used to decide whether
;;  UCT-SEARCH should print out stats about the current round
;;  of MCTS.  The COMPETE function sets *verbose* to T; the
;;  COMPETE-NO-PRINTING function sets it to NIL.  

(defparameter *verbose* t) 

(defun uct-search
    (orig-game num-sims c)
  (let* 
      ((tree (new-mc-tree orig-game))
       (index nil))
    (dotimes (i num-sims)
      (format t "heya ~%")
      (let*
	  ((copy (copy-game orig-game))
	   (states (sim-tree copy tree c))
	   (result (sim-default copy)))
	(format t "~a ~a ~a ~%" tree states result)
	(backup (mc-tree-hashy tree) states result)
      (format t "fuck ~a ~a ~a ~a ~a ~%" copy (sim-tree copy tree c) copy tree c)))
    (format t "almost")
    (setf index (select-move (get-root-node tree) 0))
    (format t "hi")
    (cond
     (*verbose*
      (format t "Best Score: ~a~%" (svref (mc-node-veck-scores (get-root-node tree)) index))
      (format t "Score Vector: ~a~%" (mc-node-veck-scores (get-root-node tree)))
      (format t "Visits Vector: ~a~%" (mc-node-veck-visits (get-root-node tree)))))
    (svref (mc-node-veck-moves (get-root-node tree)) index)))

;;  COMPETE -- defined for you!
;; ------------------------------------------------------------------------------
;;  INPUTS:  BLACK-NUM-SIMS, the number of simulations for each of black's moves
;;           BLACK-C, the exploration/exploitation constant used by black
;;           WHITE-NUM-SIMS, the number of simulations for each of white's moves
;;           WHITE-C, the exploration/exploitation constant used by white
;;  OUTPUT:  Don't care
;;  SIDE EFFECT:  Displays the entire game using UCT-SEARCH to compute best moves
;;    for both players according to the specified parameters.

(defun compete
    (black-num-sims black-c white-num-sims white-c)
  (let ((g (new-othello)))
    (while (not (game-over? g))
      (cond
       ((eq (whose-turn g) *black*)
	(format t "BLACK'S TURN!~%")
	(format t "~A~%" 
		(apply #'do-move! g nil (uct-search g black-num-sims black-c))))
       (t
	(format t "WHITE'S TURN!~%")
	(format t "~A~%"
		(apply #'do-move! g nil (uct-search g white-num-sims white-c))))))))


;;  COMPETE-NO-PRINTING
;; --------------------------------------------------
;;  Same as COMPETE, but only shows the end result

(defun compete-no-printing
    (black-num-sims black-c white-num-sims white-c)
  (let ((g (new-othello)))
    (while (not (game-over? g))
      (cond
       ((eq (whose-turn g) *black*)
	(format t "B ")
	(apply #'do-move! g nil (uct-search g black-num-sims black-c)))
       (t
	(format t "W ")
	(apply #'do-move! g nil (uct-search g white-num-sims white-c)))))
    (format t "~%~A~%" g)))

