section "Memory model for Smart Contract"

theory memory_model_8 imports Main  "HOL-Library.Word" HOL.String  begin

type_synonym  addr = "32 word"
type_synonym  val = "8 word"
type_synonym memory = " addr \<Rightarrow> val"
type_synonym result = "val list"

(*Read/write byte  definitions *)
definition read_byte :: "addr \<Rightarrow>  memory \<Rightarrow> val" where
  "read_byte a mem = mem a"
definition write_byte :: "addr  \<Rightarrow> val \<Rightarrow> memory \<Rightarrow>  memory" where
  "write_byte  a v mem = mem (a := v)"

(* memory operations *)
datatype mem_op =  
      Read addr | 
      Write addr val |
      ReadBytes addr nat | 
      WriteBytes addr "val list"

inductive eval_mem_op:: "mem_op * memory \<Rightarrow>  result * memory \<Rightarrow> bool"(infix "\<rightarrow>" 55) where
  read_byte: "\<lbrakk> read_byte a mem = v \<rbrakk>\<Longrightarrow> (Read a, mem) \<rightarrow> ([v], mem)"|
  write_byte:"\<lbrakk> write_byte a v mem = mem' \<rbrakk>\<Longrightarrow> (Write a v, mem) \<rightarrow> ([], mem')"|
  write_bytes_emptyList:"(WriteBytes a [], mem) \<rightarrow> ([], mem)"|
  write_bytes_list:"\<lbrakk> write_byte a v mem = mem';(WriteBytes(a + 1) vl, mem')\<rightarrow> ([], mem'')\<rbrakk> \<Longrightarrow>
                 (WriteBytes a (v# vl), mem) \<rightarrow> ([], mem'')"|
  read_bytes_size0: "(ReadBytes a 0, mem) \<rightarrow> ([], mem)"|
  read_bytes_sizeN: "\<lbrakk> n > 0; read_byte a mem = v; (ReadBytes (a + 1)(n-1),mem)\<rightarrow> (vl,mem) \<rbrakk> \<Longrightarrow>
                  (ReadBytes a n, mem)\<rightarrow> (v#vl, mem)"

end