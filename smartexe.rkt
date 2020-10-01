#lang s-exp rosette

(require "solidity/solidity-parser.rkt" "solidity/solidity-printer.rkt" "solidity/solidity-machine.rkt" 
         "solidity/solidity-interpret.rkt" "memory-racket.rkt"
         json graph rosette/query/debug racket/sandbox)

(require rosette/solver/smt/boolector)
(current-solver (boolector #:logic 'QF_UFBV))

(define vandal-timeout 120)
(define synthesis-timeout 360);; 6mins

(define t1 (current-inexact-milliseconds))
;; Phase 0: Set up bitwidth for Rosette
(define BV? (bitvector 256))
(current-bitwidth #f)
(define cfg-file-loc (vector-ref (current-command-line-arguments) 0))
(define cmd (string-append "./smart_opt " cfg-file-loc))
;; (pretty-display `("exe command:", cmd))
(pretty-display cfg-file-loc)

(define cfg-str
  (with-handlers ([(lambda (v) #t) (lambda (v) 'timeout)])
    (call-with-limits vandal-timeout #f (lambda () (with-output-to-string (λ() (system cmd)))))))
(when (equal? cfg-str 'timeout)  (assert #f (string-append "vandal timeout in 2 mins!!!-->" cfg-file-loc)))
(define cfg-json (string->jsexpr cfg-str))

; (pretty-display `("Analyzing CFG: ", cfg_json))
;; Phase A: Test machine, parser, printer
;; (pretty-display "Phase A: test machine, parser, and printer for Solidity bytecode.")
(define parser (new solidity-parser%))
(define max-regs 0)
(let ([init-regs 0])
     (for ([blk-json (hash-ref cfg-json `blocks)]) 
  		  (for ([cur-inst (hash-ref blk-json `insts)])
  		  	(for ([var (filter (λ (str-arg) (string-prefix? str-arg "V")) (string-split cur-inst))])
  		  		(when (< max-regs (string->number (substring var 1))) 
		           	(set! max-regs (string->number (substring var 1)))))
     )) 
)

; (assert #f max-regs)
(define machine (new solidity-machine% [config (+ 1 max-regs)]))
(define printer (new solidity-printer% [machine machine]))

;; Phase B: Interpret concrete program with concrete inputs
;; (pretty-display "Phase B: interpret program using simulator writing in Rosette.")
;; define number of bits used for generating random test inputs
(define test-bit 4)

(define (get-sym-func bit)
  (lambda (#:min [min-v #f] #:max [max-v #f] #:const [const #f])
    (define-symbolic* var BV?)
    var))

;; create random input state
(define input-state (send machine get-state (get-sym-func test-bit)))
;; define our own input test, but memory content is random
;; modify program state to match your program state structure
;;#;(define input-state (progstate (vector ?)
                               ; (new memory-racket% [get-fresh-val (get-rand-func test-bit)])))

(define simulator-rosette (new solidity-simulator-rosette% [machine machine]))
(define synth-res (call-with-limits synthesis-timeout #f
        (lambda () (send simulator-rosette init-analyzer cfg-file-loc parser printer cfg-json input-state))))

;; (if synth-res (pretty-display `("Benchmark:", cfg-file-loc, "==>find a program:", synth-res))
    ;; (pretty-display `("Benchmark:", cfg-file-loc, "==>CAN NOT ATTACK")))

(define t2 (current-inexact-milliseconds))
(pretty-display `(Running time ,(- t2 t1)))
