#lang racket

(require parser-tools/lex
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc
	 "../parser.rkt" "../inst.rkt")

(provide solidity-parser%)

;; This is a Racket Lex Yacc parser.
;; Refer to the follow resources to complete this file.
;; - Lexer:   http://docs.racket-lang.org/parser-tools/Lexers.html
;; - Parser:  http://docs.racket-lang.org/parser-tools/LALR_1__Parsers.html
;; - Example: https://gist.github.com/danking/1068185
(define solidity-parser%
  (class parser%
    (super-new)
    (inherit-field asm-parser asm-lexer)
    (init-field [compress? #f])
    
    (define-tokens a (VAR WORD NUM REG CONTR)) ;; add more tokens
    (define-empty-tokens b (EOF EQ HOLE BLOCKHASH EQCMP COMMA CREATE THROW THROWI NOP LOG BALANCE ISZERO SGT GT SLT LT SHA3 DELEGATECALL CALLCODE CALL NOT OR
                            SELFDESTRUCT MSIZE NUMBER CALLDATACOPY CODECOPY SUB TIMESTAMP EXP DIV RETURNDATACOPY MUL AND ADD REVERT RETURNDATASIZE
                            CODESIZE EXTCODECOPY MOD XOR DIFFICULTY BYTE
                            RETURN COLON ORIGIN CALLVALUE JUMP EXTCODESIZE JUMPI SLP LC RC LP RP ADDRESS CALLDATASIZE CALLDATALOAD)) ;; add more tokens

    (define-lex-abbrevs
      (digit10 (char-range "0" "9"))
      (number10 (number digit10))
      (snumber10 (re-or number10 (re-seq "-" number16)))
      (number16 (re-or (char-range "0" "9") (char-range "a" "f")))

      (snumber16 (re-+ "0x" number16))

      (identifier-characters (re-or (char-range "A" "Z") (char-range "a" "z")))
      (identifier-characters-ext (re-or digit10 identifier-characters "_"))
      (identifier (re-seq identifier-characters 
                          (re-* (re-or identifier-characters digit10))))
      (var (re-: "%" (re-+ (re-or identifier-characters digit10))))
      (reg (re-seq (re-or "V" "S") number10))
      (contr (re-: "CALL" (re-+ (re-or identifier-characters digit10))))

      )

    ;; Complete lexer
    (set! asm-lexer
      (lexer-src-pos
       ; ? ;; add more tokens
       ("M["         (token-LP))
       ("S["         (token-SLP))
       ("]"         (token-RP))
       ("}"         (token-RC))
       ("{"         (token-LC))
       ("LT"         (token-LT))
       ("SLT"         (token-SLT))
       ("GT"         (token-GT))
       ("SGT"         (token-SGT))
       (":"         (token-COLON))
       ("ADD"       (token-ADD))
       ("BYTE"       (token-BYTE))
       ("XOR"       (token-XOR))
       ("MOD"       (token-MOD))
       ("NOT"       (token-NOT))
       ("OR"       (token-OR))
       ("AND"       (token-AND))
       ("DIV"       (token-DIV))
       ("MUL"       (token-MUL))
       ("REVERT"       (token-REVERT))
       ("SUB"       (token-SUB))
       ("CREATE"       (token-CREATE))
       ("EXP"       (token-EXP))
       ("SELFDESTRUCT" (token-SELFDESTRUCT))
       ("CALLVALUE"  (token-CONTR lexeme))
       ("MSIZE"  (token-CONTR lexeme))
       ("NUMBER"  (token-CONTR lexeme))
       ("ORIGIN"  (token-CONTR lexeme))
       ("GAS"  (token-CONTR lexeme))
       ("COINBASE"  (token-CONTR lexeme))
       ("DIFFICULTY"  (token-CONTR lexeme))
       ("GASPRICE"  (token-CONTR lexeme))
       ("GASLIMIT"  (token-CONTR lexeme))
       ("TIMESTAMP"  (token-CONTR lexeme))
       ("ADDRESS"  (token-CONTR lexeme))
       ("RETURNDATASIZE"  (token-CONTR lexeme))
       ("CODESIZE"  (token-CONTR lexeme))
       ("RETURNDATACOPY"  (token-RETURNDATACOPY))
       ("CALLDATASIZE"  (token-CONTR lexeme))
       ("CALLDATALOAD"  (token-CALLDATALOAD))
       ("CODECOPY"         (token-CODECOPY))
       ("EXTCODECOPY"         (token-EXTCODECOPY))
       ("JUMPDEST"  (token-NOP))
       ("INVALID"  (token-NOP))
       ("LOG"       (token-LOG))
       ("BALANCE"  (token-BALANCE))
       ("BLOCKHASH"  (token-BLOCKHASH))
       ("JUMPI"     (token-JUMPI))
       ("JUMP"     (token-JUMP))
       ("THROWI"     (token-THROWI))
       ("THROW"     (token-THROW))
       ("SHA3"     (token-SHA3))
       ("EXTCODESIZE"   (token-EXTCODESIZE))
       ("CALL"     (token-CALL))
       ("CALLCODE"   (token-CALL))
       ("DELEGATECALL" (token-DELEGATECALL))
       ("CALLDATACOPY" (token-CALLDATACOPY))
       ("ISZERO"    (token-ISZERO))
       ("RETURN"    (token-RETURN))
       ("STOP"    (token-NOP))
       ("NOP"    (token-NOP))
       ("EQ"         (token-EQCMP))
       ("="         (token-EQ))
       ("?"         (token-HOLE))
       (","         (token-COMMA))
       (reg         (token-REG lexeme))
       (contr       (token-CONTR lexeme))
       (snumber10   (token-NUM lexeme))
       (snumber16   (token-NUM lexeme))
       (identifier  (token-WORD lexeme))
       (whitespace   (position-token-token (asm-lexer input-port)))
       ((eof) (token-EOF))))

    ;; Complete parser
    (set! asm-parser
      (parser
       (start program)
       (end EOF)
       (error
        (lambda (tok-ok? tok-name tok-value start-pos end-pos)
          (raise-syntax-error 'parser
                              (format "syntax error at '~a' in src l:~a c:~a"
                                      tok-name
                                      (position-line start-pos)
                                      (position-col start-pos)))))
       (tokens a b)
       (src-pos)
       (grammar

        ; ? ;; add more grammar rules
        (arg  ((REG) $1)
              ((NUM) $1))

        (args ((arg) (list $1))
              ((arg args) (cons $1 $2))
              ((arg COMMA args) (cons $1 $3)))
        (instruction
          ((NUM COLON WORD args)    (inst $3 (list->vector $4)))
         ;; when parsing ?, return (inst #f #f) as an unknown instruction
         ;; (a place holder for synthesis)
          ((HOLE)         (inst #f #f))
          ((NUM COLON REG EQ LT REG REG) (inst "lt" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SLT REG REG) (inst "lt" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SLT REG NUM) (inst "lt#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ LT REG NUM) (inst "lt#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ LT NUM REG) (inst "lt##" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ LT NUM NUM) (inst "lt###" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ GT REG REG) (inst "gt" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SGT REG REG) (inst "gt" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SGT REG NUM) (inst "gt#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ GT REG NUM) (inst "gt#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ GT NUM REG) (inst "gt##" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ GT NUM NUM) (inst "gt###" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ SUB REG REG) (inst "sub" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SUB REG NUM) (inst "sub#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SUB NUM REG) (inst "sub#" (vector $1 $3 $7 $6)))
          ((NUM COLON REG EQ SUB NUM NUM) (inst "sub##" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ ADD REG REG) (inst "add" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ ADD NUM REG) (inst "add#" (vector $1 $3 $7 $6)))
          ((NUM COLON REG EQ ADD REG NUM) (inst "add#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ ADD NUM NUM) (inst "add##" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ XOR REG REG) (inst "xor" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ XOR NUM REG) (inst "xor#" (vector $1 $3 $7 $6)))
          ((NUM COLON REG EQ XOR REG NUM) (inst "xor#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ XOR NUM NUM) (inst "xor##" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ MOD REG REG) (inst "mod" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ MOD NUM REG) (inst "mod#" (vector $1 $3 $7 $6)))
          ((NUM COLON REG EQ MOD REG NUM) (inst "mod#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ MOD NUM NUM) (inst "mod##" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ DIV REG REG) (inst "div" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ DIV NUM NUM) (inst "div##" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ DIV REG NUM) (inst "div#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ DIV NUM REG) (inst "div#" (vector $1 $3 $7 $6)))

          ((NUM COLON REG EQ MUL REG REG) (inst "mul" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ MUL NUM NUM) (inst "mul##" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ MUL REG NUM) (inst "mul#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ MUL NUM REG) (inst "mul#" (vector $1 $3 $7 $6)))

          ((NUM COLON REG EQ SHA3 REG REG) (inst "sha3" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SHA3 REG NUM) (inst "sha3#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ SHA3 NUM REG) (inst "sha3#" (vector $1 $3 $7 $6)))
          ((NUM COLON REG EQ SHA3 NUM NUM) (inst "sha3##" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ AND REG REG) (inst "and" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ AND NUM NUM) (inst "and##" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ AND REG NUM) (inst "and#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ AND NUM REG) (inst "and#" (vector $1 $3 $7 $6)))

          ((NUM COLON REG EQ OR REG REG) (inst "or" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ OR NUM NUM) (inst "or##" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ OR REG NUM) (inst "or#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ OR NUM REG) (inst "or#" (vector $1 $3 $7 $6)))

          ((NUM COLON REG EQ EXP REG REG) (inst "exp" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ EXP NUM NUM) (inst "exp##" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ EXP REG NUM) (inst "exp#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ EXP NUM REG) (inst "exp#" (vector $1 $3 $7 $6)))

          ((NUM COLON REG EQ EQCMP NUM REG) (inst "eqcmp" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ EQCMP REG REG) (inst "eqcmp#" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ EQCMP REG NUM) (inst "eqcmp##" (vector $1 $3 $6 $7)))

          ((NUM COLON REG EQ CALL arg arg arg arg arg arg arg) (inst "call" (vector $1 $3 $6 $7 $8)))
          ((NUM COLON REG EQ DELEGATECALL arg arg arg arg arg arg) (inst "delegatecall" (vector $1 $3 $6 $7)))
          ((NUM COLON REG EQ LP arg RP) (inst "load" (vector $1 $3 $6)))
          ((NUM COLON LP REG RP EQ arg) (inst "store" (vector $1 $4 $7)))
          ((NUM COLON LP NUM RP EQ arg) (inst "store" (vector $1 $4 $7)))
          ((NUM COLON REG EQ SLP arg RP) (inst "sload" (vector $1 $3 $6)))

          ((NUM COLON SLP arg RP EQ arg) (inst "sstore" (vector $1 $4 $7)))
          ((NUM COLON LP arg RP EQ LC arg COMMA arg RC) (inst "nop" (vector $1)))
          ((NUM COLON LP NUM RP EQ LC args RC) (inst "store-set" (vector $1 $4 (list->vector $8))))

          ((NUM COLON REG EQ CALLDATALOAD arg) (inst "calldataload" (vector $1 $3 $6))) ; FIXME!!
          ; ((NUM COLON REG EQ CALLVALUE) (inst "eq#" (vector $1 $3)))
          ((NUM COLON REG EQ CONTR) (inst "eq#" (vector $1 $3 $5)))
          ((NUM COLON REG EQ NUM) (inst "eq#" (vector $1 $3 $5)))
          ((NUM COLON REG EQ REG) (inst "eq" (vector $1 $3 $5)))
          ((NUM COLON REG EQ LC NUM COMMA NUM COMMA NUM RC) (inst "eq#" (vector $1 $3 $6)))
          ((NUM COLON REG EQ LC NUM COMMA NUM COMMA NUM COMMA NUM RC) (inst "eq#" (vector $1 $3 $6)))
          ((NUM COLON REG EQ LC NUM COMMA NUM RC) (inst "eq#" (vector $1 $3 $6)))
          ((NUM COLON REG EQ ISZERO REG) (inst "iszero" (vector $1 $3 $6)))
          ((NUM COLON REG EQ ISZERO NUM) (inst "iszero#" (vector $1 $3 $6)))
          ((NUM COLON REG EQ ISZERO LC arg COMMA arg RC) (inst "iszero" (vector $1 $3 $7)))
          ((NUM COLON REG EQ BLOCKHASH REG) (inst "blockhash" (vector $1 $3 $6))) 
          ((NUM COLON REG EQ BLOCKHASH NUM) (inst "blockhash#" (vector $1 $3 $6))) 
          ((NUM COLON REG EQ BALANCE REG) (inst "balance" (vector $1 $3 $6))) 
          ((NUM COLON REG EQ BALANCE NUM) (inst "balance#" (vector $1 $3 $6))) 
          ((NUM COLON RETURNDATACOPY arg arg arg) (inst "nop" (vector $1))) ;FIXME: wrong
          ((NUM COLON REG EQ NOT NUM) (inst "snot#" (vector $1 $3 $6)))
          ((NUM COLON REG EQ NOT REG) (inst "snot" (vector $1 $3 $6)))
          ((NUM COLON CODECOPY arg arg arg)      (inst "codecopy" (vector $1 $4 $5 $6)))
          ((NUM COLON EXTCODECOPY arg arg arg arg)      (inst "nop" (vector $1)))
          ((NUM COLON REVERT arg arg)        (inst "nop" (vector $1))) ;FIXME: wrong
          ((NUM COLON RETURN arg arg)        (inst "nop" (vector $1))) ;FIXME: wrong
          ((NUM COLON LOG arg arg arg)          (inst "nop" (vector $1)))
          ((NUM COLON LOG arg arg arg arg)          (inst "nop" (vector $1)))
          ((NUM COLON LOG arg arg arg arg arg)          (inst "nop" (vector $1)))
          ((NUM COLON LOG args)          (inst "nop" (vector $1)))
          ((NUM COLON NOP)        (inst "nop" (vector $1))) 
          ((NUM COLON JUMPI arg REG) (inst "jumpi" (vector $1 $4 $5)))
          ((NUM COLON JUMPI NUM NUM) (inst "jumpi##" (vector $1 $4 $5)))
          ((NUM COLON THROWI REG) (inst "throw" (vector $1 $4)))
          ((NUM COLON THROW) (inst "nop" (vector $1)))
          ((NUM COLON THROW NUM) (inst "nop" (vector $1)))
          ((NUM COLON JUMP arg) (inst "jump" (vector $1 $4)))
          ((NUM COLON JUMP LC args RC) (inst "jump##" (list->vector $5)))
          ((NUM COLON REG EQ CREATE NUM REG REG) (inst "create" (vector $1 $3 $6 $7 $8)))
          ((NUM COLON REG EQ CREATE NUM REG NUM) (inst "create#" (vector $1 $3 $6 $7 $8)))
          ((NUM COLON REG EQ EXTCODESIZE REG) (inst "extcodesize" (vector $1 $3 $6)))
          ((NUM COLON REG EQ EXTCODESIZE NUM) (inst "extcodesize#" (vector $1 $3 $6)))
          ((NUM COLON CALLDATACOPY arg arg arg) (inst "nop" (vector $1))) ;;FIXME

          ((NUM COLON REG EQ BYTE NUM REG) (inst "byte#" (vector $1 $3 $7 $6)))
          ;; comp_ec2_12_15.txt:"parser error: 0x49d8: V4833 = EQ 0x0 0x0"
          ;; comp_ec2_12_15.txt:"parser error: 0x1511: V2183 = SIGNEXTEND 0x13 V2138"
          ;; comp_ec2_12_15.txt:"parser error: 0x1ed: V124 = CREATE S9 V122 V123"
          ;; comp_ec2_12_15.txt:"parser error: 0x1da: V183 = CREATE S5 V179 V182"
          ;; comp_ec2_12_15.txt:"parser error: 0x8f4: CODECOPY V798 0x0 V786"
          ((NUM COLON SELFDESTRUCT REG) (inst "selfdestruct" (vector $1 $4)))
          ((NUM COLON SELFDESTRUCT NUM) (inst "nop" (vector $1)))
         ) 
        
        (code   
         (() (list))
         ((instruction code) (cons $1 $2)))

        (program
         ((code) (list->vector $1)))
       )))


    ;;;;;;;;;;;;;;;;;;;;;;;;; For cooperative search ;;;;;;;;;;;;;;;;;;;;;;;
    #|
    ;; Required method if using cooperative search driver.
    ;; Read from file and convert file content into the format we want.
    ;; Info usually includes live-out information.
    ;; It can also contain extra information such as precondition of the inputs.
    (define/override (info-from-file file)
      ? ;; modify this function

      ;; Example
      ;; read from file
      (define lines (file->lines file))
      (define live-out (string-split (first lines) ","))
      live-out)
    |#

    ))

