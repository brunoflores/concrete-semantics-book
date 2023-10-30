section "IMP: A Simple Imperative Language"

theory Com imports BExp begin

text "The abstract syntax of IMP:"

datatype com =
  SKIP
| Assign vname aexp ("_ ::= _" [1000, 61] 61)
| Seq com com       ("_;;/ _" [60, 61] 60)
| If bexp com com   ("(IF _/ THEN _/ ELSE _)" [0, 0, 61] 61)
| While bexp com    ("(WHILE _/ DO _)" [0, 61] 61)

(* Example IMP program *)
value "''x'' ::= Plus (V ''y'') (N 1);; ''y'' ::= N 2"

end
