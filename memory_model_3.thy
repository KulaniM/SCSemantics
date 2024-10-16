section "Memory model for Smart Contract"

theory memory_model_3 imports "../IMP/Star" Comm_3 "HOL-Library.Word" begin

typedef word32 = "(32::len) word"

type_synonym addr = nat
type_synonym val = int                    
type_synonym storage = "addr \<Rightarrow> val"
type_synonym memory = "addr \<Rightarrow> val"
typedecl extra_store

type_synonym s_env = "vname \<Rightarrow> addr"
type_synonym pgstate = "s_env * storage * memory * extra_store"
  
fun aval :: "aexp \<Rightarrow> pgstate \<Rightarrow>  int" where
"aval (N i) s =  i"| 
"aval (V x) (env, store, mem, extra) = (case env x of addr \<Rightarrow> store addr)" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval  a\<^sub>1 s + aval  a\<^sub>2 s"

fun bval :: "bexp \<Rightarrow> pgstate \<Rightarrow> bool" where
"bval (Bc v) s = v" |                              
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval  a\<^sub>1  s < aval  a\<^sub>2 s)"

fun encode_ptype :: "ptype \<Rightarrow> int" where
"encode_ptype (TInt i) = i "|
"encode_ptype (TBool True) = -1 "|
"encode_ptype (TBool False) = -2 "

fun updateLocalState :: "pgstate \<Rightarrow> param list \<Rightarrow> ptype list \<Rightarrow> pgstate " where
"updateLocalState s [][] = s"|
"updateLocalState  (env, store, mem, extra)(p#pl)(i#il) = 
          updateLocalState (env, store, mem(env (fst p):= encode_ptype i), extra) pl il"|
"updateLocalState s _ _ = s"




end