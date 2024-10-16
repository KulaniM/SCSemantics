section "Small-Step Semantics of Commands for Smart Contract"

theory Small_Step_SC imports "../IMP/Star" Comm   begin

 (* function  has_permission *)
type_synonym modifier = String.string
type_synonym validModifier = String.string

fun has_permission :: "fname \<Rightarrow> modifier \<Rightarrow> validModifier list \<Rightarrow>bool" where
  "has_permission f _ [] = False"|
  "has_permission f m (vm#vmodifers) = (if m = vm then True else has_permission f m vmodifers) "

 (* instance for contract *)
definition contract1 :: contract where
  "contract1 = Contract[(''address'',''address1''),(''balance'',''300'')]"


subsection "The transition relation"

inductive
  small_step:: "comm * state \<Rightarrow> comm * state \<Rightarrow>bool" (infix "\<rightarrow>" 55)  where

Assignment: "(x::= a, s)\<rightarrow>(SKIP, s(x:= aval a s))"|

Sequence_1: "(SKIP;;c1, s) \<rightarrow> (c1, s)"|
Sequence_2: "(c1,s)\<rightarrow>(c1',s') \<Longrightarrow> (c1;;c2, s) \<rightarrow> (c1';;c2, s')"|
 (* If *)
IfTrue: "bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2, s)\<rightarrow> (c1, s)"|
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<rightarrow> (c2, s)"|
 (* While *)
While: "(WHILE b DO c1, s)\<rightarrow> (IF b THEN c1;; WHILE b DO c1 ELSE SKIP, s)"|
WhileTrue: "bval b s \<Longrightarrow> (IF b THEN c1;; WHILE b DO c1 ELSE SKIP, s)\<rightarrow>(c1;; WHILE b DO c1, s)"|
WhileFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c1;; WHILE b DO c1 ELSE SKIP, s)\<rightarrow>(SKIP1, s)"|

 (* Expression/Operator Evaluation *)
OperatorLeft: "(EVALEXP a1 a2, s)\<rightarrow> (EVALEXP (N n1) a2,s)"|
OperatorRight: "(EVALEXP (N n1) a2, s)\<rightarrow> (EVALEXP (N n1) (N n2),s)"|
PlusOperator: "(EVALEXP (N n1) (N n2), s) \<rightarrow> (v::= N (n1+n2), s)"|
MinusOperator: "(EVALEXP (N n1) (N n2), s) \<rightarrow> (v::= N (n1-n2), s)"|

 (* Function Call *)
Function_Eval_Arg_1: "(CALL fname (a1#args),s)\<rightarrow>(CALL fname ((N n1)#args),s')"|
Function_Eval_Arg_2: "(CALL fname ((N n1)#a2#args),s)\<rightarrow>(CALL fname ((N n1)#(N n2)#args),s')"|
Function_Eval_Args_Subst:"(UPDATEARGS fname (p1#params)(v1#vals),s') \<rightarrow>(fbody[s'(p1:=v1)],s')"|
Function_Body_Execution: "(c1,s')\<rightarrow> (c1',s'') \<Longrightarrow>(c1;;c2,s')\<rightarrow> (c1';;c2,s'')"|
Function_Return_Result: "(RETURN r a,s')\<rightarrow> (SKIP, s'(r:= aval a s'))"|

 (* Function Modifiers *)
Fun_PermisnCheck_True: "has_permission f m vmlist \<Longrightarrow> (PERMISSIONCHECK fname modifier, s)\<rightarrow> (CALL fname a1#args, s)"|
Fun_PermisnCheck_False: "\<not>has_permission f m vmlist \<Longrightarrow> (PERMISSIONCHECK fname modifier, s)\<rightarrow> (SKIP, s)"|

 (* Inheritance *)
Get_Func_By_Instance: "(GETFUNCTION fname contract1 params,s)\<rightarrow>(CALL fname a1#args, s)"


end



