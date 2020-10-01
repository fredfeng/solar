#lang s-exp rosette
(require "../simulator-rosette.rkt" "../ops-rosette.rkt" 
  "../inst.rkt" "solidity-machine.rkt" graph rosette/lib/match rosette/lib/angelic)
(require (prefix-in unsafe- (only-in racket box set-box! unbox)))

(provide solidity-simulator-rosette%)

;; Types of different vulnerabilities
(define vul-time #f)
(define vul-access #f) ;; msg.sender flows to storage.
(define vul-reentrance #f)
(define vul-integer #f)
(define vul-random #f)
(define vul-short-addr #f)
(define vul-dos #f)
(define vul-uncheck #f)
(define vul-tod #f)
(define vul-attack #f)
(define vul-teether #f)
(define vul-blknum #f)
(define vul-call-value #f)
(define vul-call-addr #f)
(define vul-overflow #f)
(define store-taint #f)

(define dao-stack empty)
(define BV8? (bitvector 8))
(define dao-bit (bv 0 2))
;; (define storage-vars (list))

(define (reset-vul)
  (set! vul-time #f)
  (set! vul-access #f)
  (set! vul-reentrance #f)
  (set! vul-integer #f)
  (set! vul-random #f)
  (set! vul-short-addr #f)
  (set! vul-dos #f)
  (set! vul-uncheck #f)
  (set! dao-bit (bv 0 2))
  (set! vul-tod #f))

;; extract a list of constants from (choose* 1 2 3)
(define (extract-const-from-expr t)
  (foldl (lambda (x acc)
           (if (expression? x)
               (append acc (extract-const-from-expr x))
               (if (bv? x)
                   (append acc (list x))
                   acc)))
         (list)
         (match t
           [(expression op child ...) child]
           [_                      (list t)])))

(define transfer-limit (bv 2300 256))

(define solidity-simulator-rosette%
  (class simulator-rosette%
    (super-new)
    (init-field machine)
    (override interpret performance-cost get-constructor)

    (define (get-constructor) solidity-simulator-rosette%)

    (define bit (get-field bitwidth machine))
    (define nop-id (get-field nop-id machine))
    (define opcodes (get-field opcodes machine))

    (define verbose #f)
    (define synth-mode #t)
    (define summary-mode #f)
    (define program-size 2)
    (define thread-size 3) ;;parallel
    (define BV? (bitvector 256))
    (define ONE? (bv 1 BV?))
    (define ZERO? (bv 0 BV?))
    (define-symbolic sha3-app (~> BV? BV? BV?))
    (define-symbolic codecopy-app (~> BV? BV? BV? BV?))
    (define-symbolic exp-app (~> BV? BV? BV?))
    (define-symbolic blockhash-app (~> BV? BV?))
    (define-symbolic codesize-var BV?)
    (define-symbolic time-var BV?)
    (define-symbolic blk-num-var BV?)
    (define-symbolic gasprice-var BV?)
    (define-symbolic gaslimit-var BV?)
    (define-symbolic coinbase-var BV?)
    (define-symbolic difficulty-var BV?)
    ;;do not lift by Rosette.
    (define storage-vars (mutable-set))
    (define call-ret-vars (mutable-set))
    (define jmp-vars (mutable-set))

    (define (get-store-var)
      (define-symbolic* store-var BV?)
      (set-add! storage-vars store-var)
      store-var)

    (define (get-callret-var)
      (define-symbolic* call-ret-var BV?)
      (set-add! call-ret-vars call-ret-var)
      call-ret-var)

    (define (check-interfere src sink)
      ;; (pretty-display `("checking interfere:", src, sink))
      (define-symbolic s1 BV?)
      (define-symbolic s2 BV?)
      ;;substitution in Rosette.
      (define expr1 (evaluate sink (sat (hash src s1))))
      (define expr2 (evaluate sink (sat (hash src s2))))
      ;; (printf "e1=~a e2=~a" expr1 expr2)
      ;; (define formula (and (not (bveq s1 s2)) (bveq expr1 expr2)))
      ;; (unsat? (solve (assert formula)))
      ;; checking two exprs are identical. hacky.
      (expression? (equal? expr1 expr2)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;; Helper functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Truncate x to 'bit' bits and convert to signed number.
    ;; Always use this macro when interpreting an operator.
    ; (define-syntax-rule (finitize-bit x) (finitize x bit))
    ;; (define-syntax-rule (finitize-bit x) x)

    ;; (define-syntax-rule (bvuop op)
    ;;   (λ (x) (finitize-bit (op x))))
    ;; (define-syntax-rule (bvop op)
      ;; (λ (x y) (finitize-bit (op x y))))
    (define (iszero a) (if (bveq a ZERO?) ONE? ZERO?))
    ;; (define (snot a) (finitize-bit (not a)))
    (define (eq a) a)
    (define (vlt a b) (if (bvult a b) ONE? ZERO?))
    (define (vgt a b) (if (bvugt a b) ONE? ZERO?))

    (define (vsha3 a b) (sha3-app a b))

    (define (veqcmp a b) (if (bveq a b) ONE? ZERO?))
    (define (vexp a b) (exp-app a b))

    ;; Binary operation.
    ;;Unary operation.
    (define sink-jump (list))
    (define sink-loop-head (list))
    (define sink-cast (list))
    (define nblock->count (list))
    (define parser #f)
    (define printer #f)
    (define addr->block (list))
    (define id->addr (list))
    (define method->expr (list))
    (define addr->id (list))
    (define method-list (list)) ;; all public methods
    (struct basic-block (address insts succs))
    (define (get-keys assns) (map car assns))
    (define (get-values assns) (map cdr assns))
    ;;; from James
    (define (is-member x list) (and (not (null? list)) (or (equal? x (car list)) (is-member x (cdr list)))))
    (define MAX-DEPTH 20) ;; maximum depth of the path we would explore.
    (define (flow src sink) (is-member src (symbolics sink)))
    (define scc-list (list))
    ;;Get an item from an associate list.
    (define (get-item list key) 
        (match list
          [(list) null]
          ;; [(list) #f]
          [(list cur rest ...)
            (if (equal? (car cur) key) (cdr cur) (get-item rest key))
          ]))

    ;;thanks to Emina. op: || or &&
    (define (smart-query X Y op interferes?)
        (apply op
          (for*/list ([x X][y Y])
              (interferes? x y))))

    ;;Convert hashtable to assn-list for Rosette
    (define (hashtable-to-assnlist h-table)
      (foldl (λ (x result) 
                 (append result (list (cons x 
                                (hash-ref h-table x))))) 
          `() (hash-keys h-table)))

    ;; method call = opcode + args
    (struct op (opcode args) #:transparent)

    (define (take-up-to n xs)
      (define (iter xs n taken)
        (cond
          [(or (zero? n) (empty? xs)) (reverse taken)]
          [else (iter (cdr xs) (- n 1) (cons (car xs) taken))]))
      (iter xs n '()))

    (define (drop-up-to n xs)
      (define (iter xs n taken)
        (cond
          [(or (zero? n) (empty? xs)) xs]
          [else (iter (cdr xs) (- n 1) (cons (car xs) taken))]))
      (iter xs n '()))

    ;; Split xs into sublist of which max size is n.
    (define (split-into-chunks n xs)
      (if (null? xs)
          '()
          (let ((first-chunk (take-up-to n xs))
                (rest-of-list (drop-up-to n xs)))
            (cons first-chunk (split-into-chunks n rest-of-list)))))

    ;;;;;;;;;;;;;;;;;;;;Synthesis begins
    (define (attack-synthesis cfg-file-loc state prog-size)
      (define (gen-inst) (apply choose* method-list))

      (define (query-model sketch)
        ;; (output-smt #t)
        ;; (reset-vul)
        ;; (define state-out
        ;;   (if summary-mode (interpret-summary sketch state)
        ;;                    (interpret-program sketch state)))
        ;; (define cost (progstate-cost state-out))
        ;; (define last-stmt (last sketch))
        ;;attack control
        ;; (define cst (foldl (lambda (x res) (or res (flow (cdr x) (car x))))
                           ;; #f (crossproduct taint-list ctrl-args)))
        ;;timestamp
        ;; (pretty-display `("timer:", (sat? (solve (assert vul-time)))))
        ;; (define cst vul-access) ;; msg.sender flows to storage.


        ;; (define has-time? (sat? (solve (assert vul-time))))
        (define has-time? (not (empty? (filter (lambda (x) (equal? "time-var" (~v x))) (symbolics vul-time)))))
        (define has-block? (sat? (solve (assert vul-blknum))))
        (define has-gasless? gasless)
        (define has-tod? (expression? vul-tod))
        (define has-dao? (sat? (solve (assert cst))))
        (define has-attack? (sat? (solve (assert vul-attack))))
        (define batch1 (sat? (solve (assert (&& vul-overflow vul-call-value)))))
        (define batch2 (sat? (solve (assert (&& vul-overflow vul-call-addr vul-call-value)))))
        (define has-teEther? (sat? (solve (assert (|| vul-teether vul-call-value vul-call-addr)))))
        (printf "time=~a \n" vul-time)
        (printf "My benchmark=~a @timestamp=~a | blknum=~a | gasless=~a | tod=~a | dao=~a | attack=~a | teEther=~a batch1=~a batch2=~a \n"
            cfg-file-loc has-time? has-block? has-gasless? has-tod? has-dao? has-attack? has-teEther? batch1 batch2)
        cst)


      ;; main synthesis loop
      (define solution #f)
      (define has-sol #f)
      (for ([i (range 1 prog-size)] #:break has-sol)
        (let* ([sketch
                (parallel-eval method-list i thread-size)]
               [binding
                (solve (assert (query-model sketch)))])
              (begin
                  (if (sat? binding)
                      ;; (printf "binding=~a ***** map=~a\n" binding method->expr)
                      (set! solution
                            (evaluate (map (lambda (m) (get-item method->expr m)) sketch) binding))
                      (void)
                      )
                  (set! has-sol (sat? binding))
                  )))
      (when solution (pretty-display `("find a solution:", solution)))
      solution
    )

    ;;;;;;;;;;;;;;;;;;;;Syntheiss ends

    (define meth->num (make-hash))
    (define meth->reach (make-hash))
    (define meth->summary (make-hash))
    (define meth-args (mutable-set))

    (define/public (init-analyzer cfg-file-loc parser-arg printer-arg cfg-json state [ref #f])
      (set! parser parser-arg)
      (set! printer printer-arg)
      (define addr-block-hash (make-hash))
      (define blocks-raw (hash-ref cfg-json 'blocks))
      (define cfg-graph (unweighted-graph/directed (list)))

      (set! id->addr (map (λ (x y) (cons (bv x BV8?) (hash-ref y `address))) (range (length blocks-raw))
                     blocks-raw))

      (set! addr->id (map (λ (x y) (cons (hash-ref y `address) (bv x BV8?))) (range (length blocks-raw))
                     blocks-raw))

      (for ([blk-json blocks-raw])
        (begin
          (let ([cur-blk (basic-block (get-item addr->id (hash-ref blk-json `address))
                       (hash-ref blk-json `insts)
                       (map (λ (x) (get-item addr->id x)) (hash-ref blk-json `succs)))])
            (hash-set! addr-block-hash (basic-block-address cur-blk) cur-blk)))
      )

      (set! addr->block (hashtable-to-assnlist addr-block-hash))

      (for ([blk (get-keys id->addr)])
        (add-vertex! cfg-graph blk))

      (for ([blk (hash-values addr-block-hash)])
        (for ([successor (basic-block-succs blk)])
          (add-directed-edge! cfg-graph (basic-block-address blk) successor)))

      (set! scc-list (flatten (filter (lambda (x) (> (length x) 1)) (scc cfg-graph))))
      ;; (pretty-display `("cfg info: ", (get-vertices cfg-graph), " scc: ",
      ;;                                 scc-list, (scc cfg-graph), (get-edges cfg-graph)))

      (when verbose (pretty-display `("addr->block:", addr->block, id->addr)))

      ;; (for-each (lambda (x) (pretty-display `("block:", (car x), (basic-block-insts (cdr x))))) addr->block)

      (set! method-list (foldl (λ (x result)
          (append result (list (get-item addr->id (first (string-split x "-"))))))
          (list) (hash-ref cfg-json 'public_methods)))

      (define (gen-fresh-arg)
        (define-symbolic* arg BV?)
        (set-add! meth-args arg)
        arg)

      (set! method->expr
        (foldl (lambda (i cu)
              (define name (first (string-split i "-")))
              (define arg-num (string->number (second (string-split i "-"))))
              (define-symbolic* arg BV?)
              (define args (foldl (lambda (x res)
                                    (append res (list (gen-fresh-arg)))) (list) (range arg-num)))
              (define func-expr (op (get-item addr->id name) args))

              ;; (pretty-display `("debugging pair:", name, arg-num, args, func-expr))
              (append cu (list (cons (get-item addr->id name) func-expr)))
              ) (list) (hash-ref cfg-json 'public_methods)))

      (when verbose (pretty-display `("method list:", method-list, method->expr)))

      ;;Generate summary for each method
      (define (gen-summaries)
        (for ([m method-list])
              (let ([sum (progstate-summary (interpret-program (list m) state))])
                (hash-set! meth->summary m (unsafe-unbox sum)))))

      (if (empty? method-list) #f
          (if synth-mode
              (if summary-mode
                  (begin (gen-summaries)
                         (attack-synthesis cfg-file-loc state (add1 program-size)))
                  (attack-synthesis cfg-file-loc state (add1 program-size)))
              (interpret-program method-list state))))

    (define (make-table from to)
      (define-symbolic* tbl (~> from to))
      tbl)

    (define (table-ref tbl key)
      (tbl key))

    (define (table-set tbl key value)
      (lambda (k)
        (if (equal? k key)
            value
            (tbl k))))
    ;model CALL as uninterpret function: call-app(gas, addr, value)
    (define-symbolic call-app (~> BV? BV? BV? BV?))
    (define-symbolic byte-app (~> BV? BV? BV?))
    (define-symbolic extcodesize-app (~> BV? BV?))
    (define-symbolic create-app (~> BV? BV? BV? BV?))

    ;; struct for abstract instruction
    (struct store-sum (lhs rhs) #:transparent)
    (struct call-sum (id gas address wei) #:transparent)
    (struct time-sum (args) #:transparent)
    (struct balance-sum (args) #:transparent)
    (struct downcast-sum (args) #:transparent)

    (define (interpret-summary summary state [ref #f])
      (define (call-sum-inst gas addr wei ipc)
        (define call-expr (call-app gas addr wei))
        (define tod-data (smart-query (set->list storage-vars) (list call-expr) || check-interfere))
        (define tod-ctrl (smart-query (set->list storage-vars) (list ipc) || check-interfere))
        ;; (printf "data=~a, control=~a \n" tod-data tod-ctrl)
        (when (or tod-data tod-ctrl)
          (set! vul-tod #t))

        (when (or (check-interfere time-var ipc) (check-interfere time-var call-expr))
          (set! vul-time #t))

        (when (and ipc (bvugt gas transfer-limit) (bvugt wei ZERO?))
          (set! dao-bit (bvor dao-bit (bv 2 2)))))

      (define (store-sum-inst lhs rhs ipc)
        (when ipc
          (set! dao-bit (if (bvugt dao-bit (bv 0 2)) (bvor dao-bit (bv 1 2)) (bv 0 2)))))

      (for-each (lambda (arg)
        (for-each (lambda (m)
            (when (bveq arg m)
              (define m-sum (hash-ref meth->summary m))
              (when verbose (pretty-display `("working on summary method:", m, m-sum)))
              (unless (empty? m-sum)
                (for ([inst m-sum])
                  ;; (pretty-display `("pred======: ", inst))
                  (define inst-pc (car inst))
                  (define inst-s (cdr inst))
                  (match inst-s
                    [(store-sum lhs rhs) (store-sum-inst lhs rhs inst-pc)]
                    [(call-sum id gas address wei) (call-sum-inst gas address wei inst-pc)]
                    [_ (pretty-display `("what is this..."))]
                    )
                  )
                )
              ))
          method-list)) summary)

      (list))

    ;;A program is a list of method calls, represented by a list of root blockId
    (define (interpret-program program state [ref #f])
      (define summary (unsafe-box empty))
      ;; Copy vector before modifying it because vector is mutable, and
      ;; we don't want to mutate the input state.
      (define regs-out (vector-copy (progstate-regs state)))
      ; (pretty-display `("working on cfg:", root))
      ;; Set mem = #f for now.
      (define mem #f)

      (define storage-out (make-table BV? BV?))
      (define balance-out (make-table BV? BV?))

      ;; (set! block->count (foldl (lambda (x res) (append res (list (cons x 0)))) (list) (get-keys id->addr)))

      (define contract-out (vector-copy (progstate-contract state)))
      (define sink-out (vector-copy (progstate-sink state)))
      (vector-fill! sink-out #f)
      (define sink-idx (box 0))
      (define sink-pos (unbox sink-idx))
      (define cost (progstate-cost state))
      (define fun-args #f)
      (define curr-arg-idx (box -1))

      ;; Call this function when we want to reference mem. This function will clone the memory.
      ;; We do this instead of cloning memory at the begining
      ;; because we want to avoid creating new memory object when we can.
      (define (prepare-mem)
          ;; When referencing memory object, use send* instead of send to make it compatible with Rosette.
          (unless mem
                  (set! mem (send* (progstate-memory state) clone (and ref (progstate-memory ref))))))

      (define (interpret-inst code parent-block bound)
        ;; (define successors (basic-block-succs parent-block))
        ;; (pretty-display `("interpret@@@@@@ inst----: ", inst-str))
        ;; (define pre-condition (foldl (lambda (x res) (and x res)) #t (asserts)))

        (define my-inst (vector-ref (send printer encode code) 0))

        (when verbose
            (pretty-display `("interpret inst----: ", code))
            (pretty-display ">>> Source")
            (send printer print-syntax code)
            (pretty-display ">>> String-IR")
            (send printer print-struct code)
            (pretty-display `(">>> Encoded-IR", my-inst))
            (send printer print-struct my-inst)
            (newline))

        (define op (inst-op my-inst))
        (define op-name (vector-ref opcodes op))
        (define args (inst-args my-inst))

        (define (rrr f)
          (define d (vector-ref args 1))
          (define a (vector-ref args 2))
          (define b (vector-ref args 3))
          (define val (f (vector-ref regs-out a) (vector-ref regs-out b))) ;; reg [op] reg
          ;; (printf "f=~a aa=~a bb=~a myname=~a \n" f (vector-ref regs-out a) (vector-ref regs-out b) (|| (equal? (~v f) "bvadd") (equal? (~v f) "bvmul")))

          ;; (when (|| (equal? (~v f) "bvadd") (equal? (~v f) "bvmul"))
            (when (equal? (~v f) "bvmul")
            (define attack-overflow (smart-query (set->list meth-args) (list (vector-ref regs-out a) (vector-ref regs-out b)) || check-interfere))
            (when attack-overflow 
            ;; (printf "f=~a aa=~a bb=~a myname=~a \n" f (vector-ref regs-out a) (vector-ref regs-out b) (|| (equal? (~v f) "bvadd") (equal? (~v f) "bvmul")))
            (set! vul-overflow #t)))
          (vector-set! regs-out d val)
          (vector-set! regs-out d val))

        (define (rri f)
          (define d (vector-ref args 1))
          (define a (vector-ref args 2))
          (define b (vector-ref args 3))

          (define val (f (vector-ref regs-out a) b)) ;; reg [op] const
          (vector-set! regs-out d val))

        (define (rir f)
          (define d (vector-ref args 1))
          (define a (vector-ref args 2))
          (define b (vector-ref args 3))
          (define val (f a (vector-ref regs-out b))) ;; reg [op] const
          ;; (when (and (equal? op-name 'and) (or (= a 15) (= a 255)))
          ;;   (set! sink-cast (append sink-cast (list (vector-ref regs-out d)))))
          (vector-set! regs-out d val))

        (define (rii f)
          (define d (vector-ref args 1))
          (define a (vector-ref args 2))
          (define b (vector-ref args 3))
          (define val (f a b)) ;; reg [op] const
          (vector-set! regs-out d val))

        (define (rr f)
          (define d (vector-ref args 1))
          (define a (vector-ref args 2))
          (define val (f (vector-ref regs-out a))) ;; reg [op] 
                    (define vv (vector-ref regs-out a)) ;; reg [op] 
          (vector-set! regs-out d val))

        (define (ri f)
          (define d (vector-ref args 1))
          ; (define a (vector-ref args 2))
          (define a 
            (cond 
              [(equal? "CALLVALUE" (vector-ref args 2)) (vector-ref contract-out 0)]
              [(equal? "CALLER" (vector-ref args 2)) (vector-ref contract-out 1)]
              [(equal? "ORIGIN" (vector-ref args 2)) (vector-ref contract-out 1)]
              [(equal? "CALLDATASIZE" (vector-ref args 2)) (vector-ref contract-out 2)]
              [(equal? "GAS" (vector-ref args 2)) (vector-ref contract-out 3)]
              [(equal? "ADDRESS" (vector-ref args 2)) (vector-ref contract-out 4)]
              [(equal? "RETURNDATASIZE" (vector-ref args 2)) (vector-ref contract-out 5)]
              [(equal? "TIMESTAMP" (vector-ref args 2)) time-var]
              [(equal? "MSIZE" (vector-ref args 2)) (vector-ref contract-out 7)]
              [(equal? "NUMBER" (vector-ref args 2)) blk-num-var]
              [(equal? "CODESIZE" (vector-ref args 2)) codesize-var]
              [(equal? "GASPRICE" (vector-ref args 2)) gasprice-var]
              [(equal? "GASLIMIT" (vector-ref args 2)) gaslimit-var]
              [(equal? "DIFFICULTY" (vector-ref args 2)) difficulty-var]
              [(equal? "COINBASE" (vector-ref args 2)) coinbase-var]
              [else (vector-ref args 2)]
              )
            )
          (define val (f a)) ;; reg const 
          (vector-set! regs-out d val))

        (define (load)
          (define op_args (inst-args (vector-ref code 0)))
          (define d (vector-ref args 1))
          (define a (retrieve-var (vector-ref op_args 2)))
          (prepare-mem)
          ;; When referencing memory object, use send* instead of send to make it compatible with Rosette.
          (vector-set! regs-out d (send* mem load a)))

        (define (sload)
          (define op_args (inst-args (vector-ref code 0)))
          (define d (vector-ref args 1))
          (define a (retrieve-var (vector-ref op_args 2)))
          (define val (get-store-var))
          (assert (bveq val (table-ref storage-out a)))
          (vector-set! regs-out d val))

        (define (store)
          (define op_args (inst-args (vector-ref code 0)))
          (define addr (retrieve-var (vector-ref op_args 1)))
          (define val (retrieve-var (vector-ref op_args 2)))
          (prepare-mem)
          (send* mem store addr val))

        (define (store-set)
          (define addr (vector-ref args 1))
          (define val (vector-ref args 2))
          (prepare-mem)
          (send* mem store (vector-ref regs-out addr) (vector-ref regs-out val)))

        (define (sstore)
          (define op_args (inst-args (vector-ref code 0)))
          (define addr (retrieve-var (vector-ref op_args 1)))
          (define val (retrieve-var (vector-ref op_args 2)))

          (set! dao-bit (if (bvugt dao-bit (bv 0 2)) (bvor dao-bit (bv 1 2)) (bv 0 2)))
          ;; (printf "daobit-store=~a \n" dao-bit)
          (unsafe-set-box! summary (append (unsafe-unbox summary) (list (cons (pc) (store-sum addr val)))))
          (define attack-store (smart-query (set->list meth-args) (list val) || check-interfere))
          (when attack-store (set! store-taint #t))
          
          (set! storage-out (table-set storage-out addr val)))

        ;; Jump to addr if cond holds.
        (define (jumpi)
          ; (pretty-print args)
          (define dest (send printer get-addr-id (vector-ref args 1)))
          (define dest-id (get-item addr->id dest))
          (define cond (vector-ref args 2))
          (define cond-val (vector-ref regs-out cond))
          (set-add! jmp-vars cond-val)

          (define blk-id (basic-block-address parent-block))
          ;; (pretty-display `("doing jumpI.....", blk-id, "dest:", dest-id, (is-member blk-id scc-list)))
          (set! sink-loop-head (append sink-loop-head (list cond-val)))
          (set! sink-jump (append sink-jump (list cond-val)))
          ;; (pretty-display `("doing JUMPI:", (symbolics cond-val)))
          (define pred (bveq cond-val ZERO?))
          (define neg-pred (not pred))
          (define curr-succs (basic-block-succs parent-block))
          (define neg-succ (first (filter (lambda (x) (equal? dest-id x)) curr-succs)))
          (define pos-succ (first (filter (lambda (x) (not (equal? dest-id x))) curr-succs)))
          (if pred
              (interpret-block pos-succ (sub1 bound))
              (interpret-block neg-succ (sub1 bound)))
        )

        (define (jumpi##)
          ; (pretty-print args)
          (define dest (send printer get-addr-id (vector-ref args 1)))
          (define dest-id (get-item addr->id dest))
          (define cond-val (vector-ref args 2))
          (define blk-id (basic-block-address parent-block))
          (define pred (bveq cond-val ZERO?))
          (define neg-pred (not pred))
          (define curr-succs (basic-block-succs parent-block))
          (define neg-succ (first (filter (lambda (x) (equal? dest-id x)) curr-succs)))
          (define pos-succ (first (filter (lambda (x) (not (equal? dest-id x))) curr-succs)))
          (if pred
              (interpret-block pos-succ (sub1 bound))
              (interpret-block neg-succ (sub1 bound)))
        )

        (define (jump)
          ;; (define dest (send printer get-addr-id (vector-ref args 1)))
          (define curr-one-succ (list-ref (basic-block-succs parent-block) 0)) ; only has one successor.
          (interpret-block curr-one-succ (sub1 bound))
        )

        (define (throw)
          (define curr-one-succ (list-ref (basic-block-succs parent-block) 0)) ; only has one successor.
          (interpret-block curr-one-succ (sub1 bound))
          )

        (define (jump##)
          (for ([i (range 0 (vector-length args))])
            (let* ([a1 (send printer get-addr-id (vector-ref args i))]
                   [succ1 (get-item addr->id a1)])
              (when (< i 3) (interpret-block succ1 (sub1 bound))))))

        (define (extcodesize)
          (define dest (vector-ref args 1))
          (define a (vector-ref args 2))
          (define val (vector-ref regs-out a))
          (vector-set! regs-out dest (extcodesize-app val)))
        (define (extcodesize#)
          (define dest (vector-ref args 1))
          (define val (vector-ref args 2))
          (vector-set! regs-out dest (extcodesize-app val)))

        (define (selfdestruct)
          (define a (vector-ref args 1))
          (define val (vector-ref regs-out a))
          (define attack-data (smart-query (set->list meth-args) (list val) || check-interfere))
          (when attack-data (set! vul-teether #t))
          (vector-set! sink-out sink-pos val)
          (set-box! sink-idx (add1 sink-pos))
         )

        (define (calldataload)
          (define loc (send printer get-addr-id (vector-ref args 0)))
          (define a (vector-ref args 1))
          (define b (vector-ref args 2))
          ; (pretty-display `("calldataload=====", loc, a, b, funarg, (send* fun-args load b)))
          (define idx (unbox curr-arg-idx))
          (define val (list-ref fun-args idx))
          (set-box! curr-arg-idx (add1 idx))
          (vector-set! regs-out a val))

        (define (create#)
          (define dest (vector-ref args 1))
          (define value (vector-ref args 2))
          (define offset (vector-ref regs-out (vector-ref args 3)))
          (define len (vector-ref args 4))
          (vector-set! regs-out dest (create-app value offset len)) 
        )

        (define (create)
          (define dest (vector-ref args 1))
          (define value (vector-ref args 2))
          (define offset (vector-ref regs-out (vector-ref args 3)))
          (define len (vector-ref regs-out (vector-ref args 4)))
          (vector-set! regs-out dest (create-app value offset len)) 
        )

        (define (retrieve-var var)
          (cond
            [(string-prefix? var "V") (vector-ref regs-out (string->number (substring var 1)))]
            [(string-prefix? var "S") (vector-ref regs-out (string->number (substring var 1)))]
            [(string-prefix? var "0x")
             (bv (string->number (string-replace var "0x" "#x")) BV?)]
            [else (raise (format "Undefined argument for ~a" var))]))

        (define (delegatecall)
          (define op_args (inst-args (vector-ref code 0)))
          (define dest (vector-ref args 1))
          (define gas (retrieve-var (vector-ref op_args 2)))
          (define addr (retrieve-var (vector-ref op_args 3)))
          (define attack-data (smart-query (set->list meth-args) (list addr) || check-interfere))
          (when attack-data (set! vul-attack #t))
          ;; (printf "Working on delegatecall: gas=~a addr=~a args=~a\n" gas addr meth-args)
          (vector-set! regs-out dest (call-app gas addr ZERO?)))

        (define (call)
          (define op_args (inst-args (vector-ref code 0)))
          (define dest (vector-ref args 1))
          (define gas (retrieve-var (vector-ref op_args 2)))
          (define addr (retrieve-var (vector-ref op_args 3)))
          (define amount (retrieve-var (vector-ref op_args 4)))
          (define call-expr (call-app gas addr amount))
          (define retvar (get-callret-var))
          (assert (bveq retvar call-expr))
          (set-add! call-ret-vars retvar)

          (define blknum-data (check-interfere blk-num-var call-expr))
          (when blknum-data (set! vul-blknum #t))
          ;; (define blknum-ctrl (check-interfere blk-num-var (pc)))
          ;; (printf "debug call: blknumber=~a ctrl=~a" blknum-data blknum-ctrl)

          (define t1 (current-inexact-milliseconds))
          (define tod-data (smart-query (set->list storage-vars) (list call-expr) || check-interfere))
          (define tod-ctrl (smart-query (set->list storage-vars) (list (pc)) || check-interfere))
          (define t2 (current-inexact-milliseconds))
          ;; (printf "TOD query = ~a \n" (- t2 t1))

          ;; (printf "data=~a, control=~a \n" tod-data tod-ctrl)
          (when (or tod-data tod-ctrl)
            (set! vul-tod #t))

          (when (and (bvugt gas transfer-limit) (bvugt amount ZERO?))
            (set! dao-bit (bvor dao-bit (bv 2 2))))

          (define attack-val (smart-query (set->list meth-args) (list amount) || check-interfere))
          (define attack-addr (smart-query (set->list meth-args) (list addr) || check-interfere))
          (define store-ctrl (&& store-taint (smart-query (set->list storage-vars) (list addr) || check-interfere)))

          (when attack-val (set! vul-call-value #t))
          (when (|| store-ctrl attack-addr) (set! vul-call-addr #t))

          ;; (printf "daobit-call=~a \n" dao-bit)
          ;; (printf "debug call =~a addr=~a amount=~a \n" call-expr addr amount)
          (when (or (check-interfere time-var (pc)) (check-interfere time-var call-expr))
            (set! vul-time #t))

          (unsafe-set-box! summary (append (unsafe-unbox summary) (list (cons (pc) (call-sum dest gas addr amount)))))

          (vector-set! regs-out dest retvar))
        ;; (vector-set! regs-out dest call-expr))

        (define (codecopy)
          (define op_args (inst-args (vector-ref code 0)))
          (define a1 (retrieve-var (vector-ref op_args 1)))
          (define a2 (retrieve-var (vector-ref op_args 2)))
          (define a3 (retrieve-var (vector-ref op_args 3)))
          (codecopy-app a1 a2 a3))

        (define (balance#)
          (define d (vector-ref args 1))
          (define addr (vector-ref args 2))
          (define val (table-ref balance-out addr))
          (vector-set! regs-out d val))

        (define (balance)
          (define d (vector-ref args 1))
          (define addr (vector-ref regs-out (vector-ref args 2)))
          (define val (table-ref balance-out addr))
          (vector-set! regs-out d val))

        (define (blockhash)
          (define d (vector-ref args 1))
          (define addr (vector-ref regs-out (vector-ref args 2)))
          (define val (blockhash-app addr))
          (vector-set! regs-out d val))

        (define (blockhash#)
          (define d (vector-ref args 1))
          (define addr (vector-ref args 2))
          (define val (blockhash-app addr))
          (vector-set! regs-out d val))

        (define (byte-fun x y)
           (byte-app x y))

        (cond
         [(equal? op-name `nop)   (void)]
         [(equal? op-name `jumpi)   (jumpi)]
         [(equal? op-name `jumpi##)   (jumpi##)]
         [(equal? op-name `create)   (create)]
         [(equal? op-name `create#)   (create#)]
         [(equal? op-name `throw)   (throw)]
         [(equal? op-name `jump)   (jump)]
         [(equal? op-name `jump##)   (jump##)]
         [(equal? op-name `extcodesize)   (extcodesize)]
         [(equal? op-name `extcodesize#)   (extcodesize#)]
         [(equal? op-name `calldataload)   (calldataload)]
         [(equal? op-name `selfdestruct)   (selfdestruct)]
         [(equal? op-name `add)   (rrr bvadd)]
         [(equal? op-name `add#)  (rri bvadd)]
         [(equal? op-name `add##)  (rii bvadd)]
         [(equal? op-name `mod)   (rrr bvsmod)]
         [(equal? op-name `mod#)  (rri bvsmod)]
         [(equal? op-name `mod##)  (rii bvsmod)]
         [(equal? op-name `byte#)  (rri byte-fun)]
         [(equal? op-name `xor)   (rrr bvxor)]
         [(equal? op-name `xor#)  (rri bvxor)]
         [(equal? op-name `xor##)  (rii bvxor)]

         [(equal? op-name `shl#)  (rri bvshl)]
         [(equal? op-name `store-set) (store-set)]
         [(equal? op-name `store) (store)]
         [(equal? op-name `load)  (load)]
         [(equal? op-name `sstore) (sstore)]
         [(equal? op-name `sload)  (sload)]
         [(equal? op-name `iszero)  (rr iszero)]
         [(equal? op-name `iszero#)  (ri iszero)]
         [(equal? op-name `snot)  (rr bvnot)]
         [(equal? op-name `snot#)  (ri bvnot)]
         [(equal? op-name `sub)   (rrr bvsub)]
         [(equal? op-name `sub#)   (rri bvsub)]
         [(equal? op-name `sub##)   (rii bvsub)]
         [(equal? op-name `lt#)   (rri vlt)]
         [(equal? op-name `lt##)   (rir vlt)]
         [(equal? op-name `lt###)   (rii vlt)]
         [(equal? op-name `lt)   (rrr vlt)]
         [(equal? op-name `gt#)   (rri vgt)]
         [(equal? op-name `gt##)   (rir vgt)]
         [(equal? op-name `gt###)   (rii vgt)]
         [(equal? op-name `gt)   (rrr vgt)]
         [(equal? op-name `and)  (rrr bvand)]
         [(equal? op-name `and#)  (rri bvand)]
         [(equal? op-name `and##)  (rii bvand)]
         [(equal? op-name `or)  (rrr bvor)]
         [(equal? op-name `or#)  (rri bvor)]
         [(equal? op-name `or##)  (rii bvor)]
         [(equal? op-name `exp)  (rrr vexp)]
         [(equal? op-name `exp#)  (rri vexp)]
         [(equal? op-name `exp##)  (rii vexp)]
         [(equal? op-name `div)  (rrr bvudiv)]
         [(equal? op-name `div#)  (rri bvudiv)]
         [(equal? op-name `div##)  (rii bvudiv)]
         [(equal? op-name `div)  (rri bvudiv)]
         [(equal? op-name `mul)  (rrr bvmul)]
         [(equal? op-name `mul#)  (rri bvmul)]
         [(equal? op-name `mul##)  (rii bvmul)]
         [(equal? op-name `sha3##)  (rii vsha3)]
         [(equal? op-name `sha3#)  (rri vsha3)]
         [(equal? op-name `sha3)  (rrr vsha3)]
         [(equal? op-name `eqcmp)  (rir veqcmp)]
         [(equal? op-name `eqcmp#)  (rrr veqcmp)]
         [(equal? op-name `eqcmp##)  (rri veqcmp)]
         [(equal? op-name `eq)  (rr eq)]
         [(equal? op-name `eq#) (ri eq)]
         [(equal? op-name `call)  (call)]
         [(equal? op-name `codecopy)  (codecopy)]
         [(equal? op-name `balance)  (balance)]
         [(equal? op-name `balance#)  (balance#)]
         [(equal? op-name `blockhash)  (blockhash)]
         [(equal? op-name `blockhashe#)  (blockhash#)]

         [(equal? op-name `delegatecall)  (delegatecall)]
         [else (assert #f (format "simulator: undefine instruction ~a" op))])
        op-name
      )

      (define visited (make-hash))

      (define (interpret-block worker K)
        ;; (assert (> K 0) "bound!")
        (define blk-obj (get-item addr->block worker))
        (define (parse-code inst-str)
          (define code
            (with-handlers ([(lambda (v) #t) (lambda (v) 'parser-error)])
              (send parser ir-from-string inst-str)))
            code)
        (unless (hash-has-key? visited worker)
          (hash-set! visited worker 1)
          (when verbose
            (pretty-display `("interpret block----: ", K,  worker, (get-item id->addr worker))))
          (define last-op (for/last ([x (basic-block-insts blk-obj)])
                            (define inst-code (parse-code x))
                            (unless (equal? 'parser-error inst-code)
                              (interpret-inst inst-code blk-obj K))
                            ))
          (define successors (basic-block-succs blk-obj))
          (unless (or (empty? successors) (equal? 'jump last-op))
            (interpret-block (first successors) (sub1 K)))
        )
      )

      (define (exe-m m)
        (set! dao-stack empty)
        (define fun-expr (get-item method->expr m))
        (set! fun-args (op-args fun-expr))
        (set-box! curr-arg-idx 0)
        (hash-clear! visited)
        (interpret-block m MAX-DEPTH)
        ;; (pretty-display `("method counting:", m, " original:", (hash-ref meth->num m), " actual:", ccc))
      )

      (for-each (lambda (arg)
        (for-each (lambda (m)
           (when (bveq arg m)
            (when verbose (pretty-display `("working on method:", m)))
            (exe-m m)
           ))
                  (extract-const-from-expr arg)
                  )) program)

      ;; If mem = #f (never reference mem), set mem before returning.
      (unless mem (set! mem (progstate-memory state)))
      (progstate regs-out mem cost contract-out storage-out sink-out balance-out summary)
      )

    ;;;;;;;;;;;;;;;;;;;;;;;;;;; Required methods ;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Interpret a given program from a given state.
    ;; 'program' is a vector of 'inst' struct.
    ;; 'ref' is optional. When given, it is an output program state returned from spec.
    ;; We can assert something from ref to terminate interpret early.
    ;; This can help prune the search space.
    (define (interpret program state [ref #f])
         (void)
      )

    ;; Estimate performance cost of a given program.
    (define (performance-cost program)
      ; ? ;; modify this function
      (void))
    ))
