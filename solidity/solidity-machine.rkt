#lang racket

(require "../machine.rkt" "../special.rkt")

(provide solidity-machine%  (all-defined-out))

;;;;;;;;;;;;;;;;;;;;; program state macro ;;;;;;;;;;;;;;;;;;;;;;;;
;; This is just for convenience.
(define-syntax-rule
  (progstate regs memory cost contract storage sink balance summary)
  (vector regs memory cost contract storage sink balance summary))

(define-syntax-rule (progstate-regs x) (vector-ref x 0))
(define-syntax-rule (progstate-memory x) (vector-ref x 1))
(define-syntax-rule (progstate-cost x) (vector-ref x 2))
(define-syntax-rule (progstate-contract x) (vector-ref x 3))
(define-syntax-rule (progstate-storage x) (vector-ref x 4))
(define-syntax-rule (progstate-sink x) (vector-ref x 5))
(define-syntax-rule (progstate-balance x) (vector-ref x 6))
(define-syntax-rule (progstate-summary x) (vector-ref x 7))

(define-syntax-rule (set-progstate-regs! x v) (vector-set! x 0 v))
(define-syntax-rule (set-progstate-memory! x v) (vector-set! x 1 v))
(define-syntax-rule (set-progstate-cost! x v) (vector-set! x 2 v))
(define-syntax-rule (set-progstate-contract! x v) (vector-set! x 3 v))
(define-syntax-rule (set-progstate-storage! x v) (vector-set! x 4 v))
(define-syntax-rule (set-progstate-sink! x v) (vector-set! x 5 v))
(define-syntax-rule (set-progstate-balance! x v) (vector-set! x 6 v))
(define-syntax-rule (set-progstate-summary! x v) (vector-set! x 7 v))


(define solidity-machine%
  (class machine%
    (super-new)
    (inherit-field bitwidth random-input-bits config)
    (inherit init-machine-description define-instruction-class finalize-machine-description
             define-progstate-type define-arg-type
             ; update-progstate-ins kill-outs
             )
    (override get-constructor progstate-structure display-state)

    (define (get-constructor) solidity-machine%)

    (unless bitwidth (set! bitwidth 32))
    (set! random-input-bits bitwidth)

    ;;;;;;;;;;;;;;;;;;;;; program state ;;;;;;;;;;;;;;;;;;;;;;;;
    (define (progstate-structure)
      ; ? ;; modify this function to define program state

      ;; Example:
      ;; Program state has registers and memory.
      ;; config = number of registers in this example.
      (progstate (for/vector ([i config]) 'reg)
                 (get-memory-type)
                 `cost  ; gas consumption
                 (for/vector ([i 9]) 'contract)
                 ;; (for/vector ([i 40]) 'storage)
                 (list)
                 (for/vector ([i 10]) 'sink)
                 (list)
                 (list)
                 ))

    ;; Pretty print progstate.
    (define (display-state s)
      (pretty-display "REGS:")
      (pretty-display (progstate-regs s))
      ; (pretty-display (filter (lambda (arg) (> (string-length (~v arg)) 6)) (vector->list (progstate-regs s))))
      (pretty-display "MEMORY:")
      (pretty-display (progstate-memory s))
      (pretty-display `("Contract: ", (progstate-contract s)))
      (pretty-display (format "Gas-cost: ~a" (progstate-cost s)))
      (pretty-display "Storage:")
      (pretty-display (progstate-storage s))
      (pretty-display `("Sink: ", (progstate-sink s)))
      )

    (define-progstate-type
      'reg 
      #:get (lambda (state arg) (vector-ref (progstate-regs state) arg))
      #:set (lambda (state arg val) (vector-set! (progstate-regs state) arg val)))


    ; Contract and transaction-related data structures.
    ; 0: CALLVALUE | 1: CALLDATASIZE
    (define-progstate-type
      'contract 
      #:get (lambda (state arg) (vector-ref (progstate-contract state) arg))
      #:set (lambda (state arg val) (vector-set! (progstate-contract state) arg val)))

    (define-progstate-type
      (get-memory-type)
      #:get (lambda (state) (progstate-memory state))
      #:set (lambda (state val) (set-progstate-memory! state val)))

    ;; (define-progstate-type
    ;;   'storage
    ;;   #:get (lambda (state arg) (table-ref (progstate-storage state) arg))
    ;;   #:set (lambda (state arg val) (table-set (progstate-storage state) arg val)))

    ;; (define-progstate-type
    ;;   'storage
    ;;   #:get (lambda (state arg) (table-ref (progstate-balance state) arg))
    ;;   #:set (lambda (state arg val) (table-set (progstate-balance state) arg val)))

    ;; Gas consumption.
    (define-progstate-type 'cost
      #:get (lambda (state) (progstate-cost state))
      #:set (lambda (state val) (set-progstate-cost! state val))
      #:const 0
      )
    (define-progstate-type
      'sink
      #:get (lambda (state arg) (vector-ref (progstate-sink state) arg))
      #:set (lambda (state arg val) (vector-set! (progstate-sink state) arg val)))

    ;;;;;;;;;;;;;;;;;;;;; instruction classes ;;;;;;;;;;;;;;;;;;;;;;;;
    (define-arg-type 'reg (lambda (config) (range config)))
    (define-arg-type 'const (lambda (config) '(0 2 4 6 8)))
    (define-arg-type 'bit (lambda (config) '(0 1)))
    ;; try more values for const than for bit
    ; (define-arg-type
    ;   ? ;; define argument type
    ;   )

    ;; Inform GreenThumb how many opcodes there are in one instruction. 
    (init-machine-description 1)
    
    (define-instruction-class 'nop '(nop))

    ;; An example of an instruction that takes two input registers
    ;; and update one output register
    (define-instruction-class 'rrr-commute '(add)
      #:args '(reg reg reg) #:ins '(1 2) #:outs '(0) #:commute '(1 . 2))

    ;; An example of an instruction that takes an input register and a constant
    ;; and update one output register.
    ;; Notice that opcodes in different classes can't have the same name.
    (define-instruction-class 'rri '(add#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rii '(add##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr-commute '(mod)
      #:args '(reg reg reg) #:ins '(1 2) #:outs '(0) #:commute '(1 . 2))
    (define-instruction-class 'rri '(mod#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rii '(mod##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(byte#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr-commute '(xor)
      #:args '(reg reg reg) #:ins '(1 2) #:outs '(0) #:commute '(1 . 2))
    (define-instruction-class 'rri '(xor#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rii '(xor##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    ;; An example of an instruction that takes an input register and a shift constant
    ;; and update one output register
    (define-instruction-class 'rrb '(shl#)
      #:args '(reg reg bit) #:ins '(1) #:outs '(0))

    ;; An example of an instruction that accesses memory
    (define-instruction-class 'load '(load)
      #:args '(reg reg) #:ins (list 1 (get-memory-type)) #:outs '(0))

    ;; An example of an instruction that updates memory
    (define-instruction-class 'store '(store)
      #:args '(reg reg) #:ins '(0 1) #:outs (list (get-memory-type)))

    (define-instruction-class 'store-set '(store-set)
      #:args '(reg reg) #:ins '(0 1) #:outs (list (get-memory-type)))

        ;; An example of an instruction that accesses storage
    (define-instruction-class 'sload '(sload)
      #:args '(reg reg) #:ins (list 1 (get-memory-type)) #:outs '(0))

    ;; An example of an instruction that updates storage
    (define-instruction-class 'sstore '(sstore)
      #:args '(reg reg) #:ins '(0 1) #:outs (list (get-memory-type)))
   
    (define-instruction-class 'iszero '(iszero)
      #:args '(reg reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'iszero# '(iszero#)
      #:args '(reg reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'snot '(snot)
      #:args '(reg reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'snot# '(snot#)
      #:args '(reg reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'jumpi '(jumpi)
      #:args '(const reg) #:ins '(1) #:outs '(0))
    (define-instruction-class 'jumpi## '(jumpi##)
      #:args '(const reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'jump '(jump)
      #:args '(const reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'throw '(throw)
      #:args '(const reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'jump## '(jump##)
      #:args '(const reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'extcodesize '(extcodesize)
      #:args '(const reg) #:ins '(1) #:outs '(0))
    (define-instruction-class 'extcodesize# '(extcodesize#)
      #:args '(const reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'selfdestruct '(selfdestruct)
      #:args '(const reg) #:ins '(1) #:outs '(0))

    (define-instruction-class 'eq '(eq)
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'eq '(eq#)
      #:args '(reg const) #:ins '(1) #:outs '(0))

    ; (define-instruction-class 'calldataload '(calldataload)
    ;   #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'calldataload '(calldataload)
      #:args '(reg reg) #:ins (list 1 (get-memory-type)) #:outs '(0))

    (define-instruction-class 'rri '(sub)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(sub#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(sub##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(div)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr '(div)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(div#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rii '(div##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr '(mul)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(mul#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rii '(mul##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(sha3)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rri '(sha3#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rri '(sha3##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr '(lt)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(lt#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rir '(lt##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rii '(lt###)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rri '(gt)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rri '(gt#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rir '(gt##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rii '(gt###)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr '(and)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rri '(and#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rii '(and##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr '(or)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rri '(or#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rii '(or##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr '(exp)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rri '(exp#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rii '(exp##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rir '(eqcmp)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'rrr '(eqcmp#)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))
    (define-instruction-class 'rri '(eqcmp##)
      #:args '(reg reg const) #:ins '(1 2) #:outs '(0))

    (define-instruction-class 'call '(call) 
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'codecopy '(codecopy) 
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'delegatecall '(delegatecall) 
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'create '(create) ;;FIXME
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'balance '(balance) 
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'balance# '(balance#) 
      #:args '(reg const) #:ins '(1) #:outs '(0))


    (define-instruction-class 'blockhash '(blockhash) 
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'blockhash# '(blockhash#) 
      #:args '(reg const) #:ins '(1) #:outs '(0))

    (define-instruction-class 'create# '(create#) ;;FIXME
      #:args '(reg const) #:ins '(1) #:outs '(0))
    ; (define-instruction-class
    ;   ? ;; define instruction class
    ;   )

    (finalize-machine-description)

    ))
      

