section "Memory model for Smart Contract"

theory memory_model imports "../IMP/Star" Comm begin

datatype complexVal = IntVal int| StrVal string |NullVal| ListVal "complexVal list"| RecordVal "(string * complexVal) list"
                      
type_synonym newstate = "vname \<Rightarrow> complexVal"

fun aval :: "aexp \<Rightarrow> newstate \<Rightarrow> complexVal" where
"aval (N n) s = IntVal n"| 
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = (case ( aval a\<^sub>1 s , aval a\<^sub>2 s) of 
                      (IntVal n1, IntVal n2) \<Rightarrow> IntVal (n1+n2) | _ \<Rightarrow> NullVal)"

fun bval :: "bexp \<Rightarrow> newstate \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (case ( aval a\<^sub>1 s , aval a\<^sub>2 s) of 
                      (IntVal n1, IntVal n2) \<Rightarrow>  ( n1 < n2) | _ \<Rightarrow> False)"

fun updateState :: "newstate \<Rightarrow> vname list \<Rightarrow> int list \<Rightarrow> newstate " where
"updateState s [][] = s"|
"updateState s (p#pl)(i#il) = updateState (s(p:=IntVal i)) pl il"|
"updateState s _ _ = s"
end