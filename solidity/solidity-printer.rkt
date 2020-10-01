#lang s-exp rosette

(require "../printer.rkt" "../inst.rkt" "solidity-machine.rkt")

(provide solidity-printer%)

(define solidity-printer%
  (class printer%
    (super-new)
    (inherit-field machine)
    ; (inherit encode decode)
    (override encode-inst decode-inst print-syntax-inst)

    (define BV? (bitvector 256))
    ;; Print in the assembly format.
    ;; x: string IR
    (define (print-syntax-inst x [indent ""])
      ; ? ;; modify this function

      ;; Example
      (pretty-display (format "~a ~a"
                              (inst-op x)
                              (string-join (vector->list (inst-args x)) ", "))))

    (define id->name (make-hash))

    (define (string->bitvector bt)
      (bv (string->number (string-replace bt "0x" "#x")) BV?))

    (define (name->id name)
      ; (pretty-display `(name->id ,name))
      (cond
       [(string->number name)
        (string->number name)]
       
       [(and (> (string-length name) 1) (equal? (substring name 0 1) "V"))
        (string->number (substring name 1))]

        [(and (> (string-length name) 1) (equal? (substring name 0 1) "S")) ;;this could be unsound and overwrite V0 and V1
        (string->number (substring name 1))]

       [(equal? name "CALLVALUE") name]
       [(equal? name "CALLER") name]
       [(equal? name "ORIGIN") name]
       [(equal? name "MSIZE") name]
       [(equal? name "NUMBER") name]
       [(equal? name "CALLDATASIZE") name]
       [(equal? name "GAS") name]
       [(equal? name "ADDRESS") name]
       [(equal? name "RETURNDATASIZE") name]
       [(equal? name "CODESIZE") name]
       [(equal? name "TIMESTAMP") name]
       [(equal? name "GASLIMIT") name]
       [(equal? name "DIFFICULTY") name]
       [(equal? name "GASPRICE") name]
       [(equal? name "COINBASE") name]

        ;;Convert hexadecimal string to number in racket.
       [(equal? (substring name 0 2) "0x")
        (begin (hash-set! id->name (string->bitvector name) name)
               (string->bitvector name))]

       [else
        (raise (format "encode: name->id: undefined for ~a" name))]))

    (define/public (get-addr-id val)
        (hash-ref id->name val)
      )

    ;; Convert an instruction x from string-IR to encoded-IR format.
    (define (encode-inst x)
      ; ? ;; modify this function
      ;; Example
      (define opcode-name (inst-op x))

      (cond
        [(equal? opcode-name "nop") (inst (get-field nop-id machine) (vector-map name->id (inst-args x)))]
       [opcode-name
        (define args (inst-args x))
        (define last-arg (vector-ref args (sub1 (vector-length args))))

        ;; If last arg is not a register, append "#" to opcode-name.
        ;; This is for distinguishing instructions that take (reg reg reg) vs (reg reg const).
        ;; They need distinct opcode names.
        ; (unless (equal? (substring last-arg 0 1) "V")
        ;         (set! opcode-name (string-append opcode-name "#")))

        ;; A function to convert argument in string format to number.
        (define (convert-arg arg)
          (if (equal? (substring arg 0 1) "r")
              (string->number (substring arg 1))
              (string->number arg)))

        (define op-id (send machine get-opcode-id (string->symbol opcode-name)))

        (inst (send machine get-opcode-id (string->symbol opcode-name))
              ;; get-opcode-id takes symbol (not string) as argument
              (vector-map name->id args))]

       ;; opcode-name is #f, x is an unknown instruction (a place holder for synthesis)
       ;; just return x in this case
       [else x])
      )


    ;; Convert an instruction x from encoded-IR to string-IR format.
    (define (decode-inst x)
      ; ? ;; modify this function
      ;; Example
      (define opcode-id (inst-op x))
      ;; get-opcode-name returns symbol, so we need to convert it to string
      (define opcode-name (symbol->string (send machine get-opcode-name opcode-id)))
      (define str-len (string-length opcode-name))
      (define arg-types (send machine get-arg-types opcode-id))
      (define args (inst-args x))

      ;; Remove #
      (when (equal? "#" (substring opcode-name (sub1 str-len)))
            (set! opcode-name (substring opcode-name 0 (sub1 str-len))))

      (define new-args
        (for/vector ([arg args] [type arg-types])
                    (cond
                     [(equal? type 'reg) (format "r~a" arg)]
                     [else (number->string arg)])))

      (cond
       [(equal? opcode-name "nop") (inst opcode-name (vector))]
       [else
      (inst opcode-name new-args)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;; For cooperative search ;;;;;;;;;;;;;;;;;;;;;;;
    #|
    ;; Convert live-out (the output from parser::info-from-file) into string. 
    ;; The string will be used as a piece of code the search driver generates as
    ;; the live-out argument to the method superoptimize of 
    ;; stochastics%, forwardbackward%, and symbolic%.
    ;; The string should be evaluated to a program state that contains 
    ;; #t and #f, where #t indicates that the corresponding element is live.
    (define/override (output-constraint-string live-out)
      ? ;; modify this funcion.
      
      ;; Example:
      ;; Method encode-live is implemented below, returning
      ;; live infomation in a program state format.
      (format "(send printer encode-live '~a)" live-out))

    ;; Convert liveness infomation to the same format as program state.
    (define/public (encode-live x)
      ? ;; modify this funcion.
      
      ;; Example:
      ;; If x is a list, iterate over elements in x, and set those elements to be live.
      (define reg-live (make-vector (send machine get-config) #f))
      (define mem-live #f)
      (for ([v x])
           (cond
            [(number? v) (vector-set! reg-live v #t)]
            [(equal? v 'memory) (set! mem-live #t)]))
      (progstate reg-live mem-live))
    
    ;; Return program state config from a given program in string-IR format.
    ;; program: string IR format
    ;; output: program state config
    (define/override (config-from-string-ir program)
      ? ;; modify this funcion.
      
      ;; Example:
      ;; config = number of registers
      ;; Find the highest register ID and return that as a config
      (define max-reg 0)
      (for* ([x program]
	     [arg (inst-args x)])
            (when (equal? "r" (substring arg 0 1))
                  (let ([id (string->number (substring arg 1))])
                    (when (> id max-reg) (set! max-reg id)))))
      (add1 max-reg))
    |#
    
    ))

