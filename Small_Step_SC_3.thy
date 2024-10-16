section "Small-Step Semantics of Commands for Smart Contract"

theory Small_Step_SC_3 
  
imports "../IMP/Star" Comm_3 memory_model_3 begin

(* function  has_permission *)
type_synonym modifier = String.string
type_synonym validModifier = String.string

fun has_permission :: "fname \<Rightarrow> modifier \<Rightarrow> validModifier list \<Rightarrow>bool" where
  "has_permission f _ [] = False"|
  "has_permission f m (vm#vmodifiers) = (if m = vm then True else has_permission f m vmodifiers) "

(* function  arg_evaluation *)
fun arg_evaluation :: "arg list \<Rightarrow> pgstate \<Rightarrow> ptype list" where
  "arg_evaluation[] _ = [] "|
  "arg_evaluation (a#args) ps = (case a of 
                                AExpArg e \<Rightarrow> TInt( aval e ps) # arg_evaluation args ps|
                                BExpArg b \<Rightarrow> TBool( bval b ps) # arg_evaluation args ps )"

(* function  convert command list to a sequence of commands *)
fun comm_list_to_seq :: "comm list \<Rightarrow> comm" where
  "comm_list_to_seq [] = SKIP"|
  "comm_list_to_seq [c] = c"|
  "comm_list_to_seq (c#cmds) = Seq c (comm_list_to_seq cmds)"

(* retrive function given func env for parent and child classes   *)
fun lookup_function :: "func_env \<Rightarrow> func_env \<Rightarrow> fname \<Rightarrow> func_def option" where
  "lookup_function child_env parent_env fname = (case child_env fname of Some f \<Rightarrow> Some f |
                                                 None \<Rightarrow> parent_env fname)"

subsection "The transition relation"

inductive
  small_step:: "func_env \<Rightarrow> comm * pgstate \<Rightarrow> comm * pgstate \<Rightarrow>bool" ( "_ o _ \<rightarrow> _" 55) for \<Gamma>::func_env  where

Assignment: "\<Gamma> o (x ::= a, ps) \<rightarrow> (SKIP, (env, store(x := aval a ps), mem, extra))"|

Sequence_1: "\<Gamma> o (SKIP;;c1, ps)\<rightarrow> (c1, ps)"|
Sequence_2: "\<Gamma> o (c1,ps)\<rightarrow>(c1',ps') \<Longrightarrow> \<Gamma> o (c1;;c2, s)\<rightarrow>(c1';;c2, ps')"|
 (* If *)                                                                
IfTrue: "bval b ps \<Longrightarrow>\<Gamma> o (IF b THEN c1 ELSE c2, ps)\<rightarrow>(c1, ps)"|
IfFalse: "\<not>bval b ps \<Longrightarrow>\<Gamma> o (IF b THEN c1 ELSE c2, ps)\<rightarrow>(c2, ps)"|
 (* While *)
While: "\<Gamma> o (WHILE b DO c1, ps)\<rightarrow> (IF b THEN c1;; WHILE b DO c1 ELSE SKIP, ps)"|
WhileTrue: "bval b ps \<Longrightarrow>\<Gamma> o (IF b THEN c1;; WHILE b DO c1 ELSE SKIP, ps)\<rightarrow>(c1;; WHILE b DO c1, ps)"|
WhileFalse: "\<not>bval b ps \<Longrightarrow> \<Gamma> o(IF b THEN c1;; WHILE b DO c1 ELSE SKIP, ps)\<rightarrow>(SKIP1, ps)"|

 (* Function Call - permission check *)
Permission_CheckFail:"\<not>has_permission fname modifier vmlist \<Longrightarrow> 
                      \<Gamma> o (CALL fname inputargs, ps)\<rightarrow>(ERROR permission_fail, ps)"|

 (* Function Call *)
Function_Call: "\<lbrakk>lookup_function child_func_env parent_func_env fname = Some (FuncDef modifier params body psize); 
                  arg_evaluation inputargs ps = eval_args; 
                  has_permission fname modifier vmlist \<rbrakk> \<Longrightarrow> 
               \<Gamma> o (CALL fname inputargs, ps)\<rightarrow>(CALLEXE body, 
               updateLocalState ps params eval_args)"|

Function_Call_Body: "\<Gamma> o (c1,ps)\<rightarrow>(c1',ps') \<Longrightarrow>
                     \<Gamma> o(CALLEXE (c1#commands), ps ) \<rightarrow>(c1';; comm_list_to_seq commands, ps')"


end