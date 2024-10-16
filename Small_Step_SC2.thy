section "Small-Step Semantics of Commands for Smart Contract"

theory Small_Step_SC2 
  
imports "../IMP/Star" Comm memory_model begin

(* function  has_permission *)
type_synonym modifier = String.string
type_synonym validModifier = String.string

fun has_permission :: "fname \<Rightarrow> modifier \<Rightarrow> validModifier list \<Rightarrow>bool" where
  "has_permission f _ [] = False"|
  "has_permission f m (vm#vmodifers) = (if m = vm then True else has_permission f m vmodifers) "

(* function  arg_evaluation *)
fun arg_evaluation :: "aexp list \<Rightarrow> newstate \<Rightarrow> int list" where
  "arg_evaluation[]_ = [] "|
  "arg_evaluation (a#args) s = (case aval a s of IntVal n => n # arg_evaluation args s | _ \<Rightarrow> arg_evaluation args s)"

 (* instance for contract *)
definition contract1 :: contract where
  "contract1 = Contract[(''address'',''address1''),(''balance'',''300'')]"

subsection "The transition relation"

inductive
  small_step:: "func_env \<Rightarrow> comm * newstate \<Rightarrow> comm * newstate \<Rightarrow>bool" ( "_ o _ \<rightarrow> _" 55) for \<Gamma>::func_env  where

Assignment: "\<Gamma> o (x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))"|

Sequence_1: "\<Gamma> o (SKIP;;c1, s)\<rightarrow> (c1, s)"|
Sequence_2: "\<Gamma> o (c1,s)\<rightarrow>(c1',s') \<Longrightarrow> \<Gamma> o (c1;;c2, s)\<rightarrow>(c1';;c2, s')"|
 (* If *)
IfTrue: "bval b s \<Longrightarrow>\<Gamma> o (IF b THEN c1 ELSE c2, s)\<rightarrow>(c1, s)"|
IfFalse: "\<not>bval b s \<Longrightarrow>\<Gamma> o (IF b THEN c1 ELSE c2, s)\<rightarrow>(c2, s)"|
 (* While *)
While: "\<Gamma> o (WHILE b DO c1, s)\<rightarrow> (IF b THEN c1;; WHILE b DO c1 ELSE SKIP, s)"|
WhileTrue: "bval b s \<Longrightarrow>\<Gamma> o (IF b THEN c1;; WHILE b DO c1 ELSE SKIP, s)\<rightarrow>(c1;; WHILE b DO c1, s)"|
WhileFalse: "\<not>bval b s \<Longrightarrow> \<Gamma> o(IF b THEN c1;; WHILE b DO c1 ELSE SKIP, s)\<rightarrow>(SKIP1, s)"|

 (* Function Call *)
Function_Call: "\<lbrakk>func_env fname = FuncDef modifier params body; arg_evaluation inputargs s = eval_args; 
                  has_permission fname modifier vmlist \<rbrakk> \<Longrightarrow> 
               \<Gamma> o (CALL fname inputargs, s)\<rightarrow>(CALLEXE body, updateState s params eval_args)"|

Function_Call_Execution: "\<Gamma> o (cmd,s)\<rightarrow> (SKIP,s') \<Longrightarrow> 
                          \<Gamma> o (CALLEXE (cmd # bdy), s)\<rightarrow> (CALLEXE bdy,s')"|

Function_Return_Result: "\<Gamma> o (RETURN r a,s')\<rightarrow> (SKIP, s'(r:= aval a s'))"


end