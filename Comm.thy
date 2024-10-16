section "IMP --- A Simple Imperative Language"

theory Comm imports "../IMP/BExp" begin

type_synonym  fname = String.string  (* Function name *)      
type_synonym  args = "aexp list"  (* Function arguments *)
type_synonym  params = "vname list"  (* Evaluated Function arguments *)
type_synonym  vals = "int list"  (* Evaluated Function arguments *)
type_synonym  modifier = String.string  (* Modifier name *) 
type_synonym  key = String.string 
type_synonym  val = String.string


record Object =
  id :: nat
  name :: string
  attributes :: "(key * val) list"
datatype contract = Contract (attributes:"(key * val) list" )

datatype
  comm = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    comm  comm       ("_;;/ _"  [60, 61] 60)
      | If     bexp comm comm   ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp comm        ("(WHILE _/ DO _)"  [0, 61] 61)
      | EvalExp   aexp aexp     ("EVALEXP _ _" [60, 61] 60)  (* evaluating  expression *)
      | FunCall fname args      ("CALL _ (_)" [1000, 61] 61)
      | UpdateArgs fname params vals ("UPDATEARGS _ (_)(_)" [1000, 61, 61] 61)
      | Return vname aexp       ("RETURN _ _" [1000, 60] 61)
      | CheckPermission fname modifier ("PERMISSIONCHECK _ _" [1000,1000] 61)
      | GetFunction fname contract params ("GETFUNCTION _ _ (_)" [1000, 1000, 61] 61)
      | CallExec "comm list"    ("CALLEXE (_)" [61])

type_synonym  body = "comm list"

datatype func_def = FuncDef "modifier" "params" "body"

type_synonym func_env = "fname \<Rightarrow> func_def"

end
