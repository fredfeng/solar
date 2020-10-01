#lang racket

(require "../parallel-driver.rkt" "../inst.rkt"
         "solidity-parser.rkt" "solidity-machine.rkt" 
         "solidity-printer.rkt"
	 ;; simulator, validator
	 "solidity-simulator-racket.rkt" 
	 "solidity-simulator-rosette.rkt"
         "solidity-validator.rkt")

(provide optimize)

;; Main function to perform superoptimization on multiple cores.
;; >>> INPUT >>>
;; code: program to superoptimized in string-IR format
;; >>> OUTPUT >>>
;; Optimized code in string-IR format.
(define (optimize code live-out search-type mode
                  #:dir [dir "output"] 
                  #:cores [cores 4]
                  #:time-limit [time-limit 3600]
                  #:size [size #f]
                  #:window [window #f]
                  #:input-file [input-file #f])
  
  (define parser (new solidity-parser%))
  (define machine (new solidity-machine%))
  (define printer (new solidity-printer% [machine machine]))
  (define simulator (new solidity-simulator-rosette% [machine machine]))
  (define validator (new solidity-validator% [machine machine] [simulator simulator]))
  (define parallel (new parallel-driver% [isa "solidity"] [parser parser] [machine machine] 
                        [printer printer] [validator validator]
                        [search-type search-type] [mode mode]
                        [window window]))

  (send parallel optimize code live-out 
        #:dir dir #:cores cores 
        #:time-limit time-limit #:size size #:input-file input-file)
  )

