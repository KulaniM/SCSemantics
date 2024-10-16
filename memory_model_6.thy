section "Memory model for Smart Contract"

theory memory_model_6 imports Main  "HOL-Library.Word" HOL.String  begin

type_synonym  addr = "32 word"
type_synonym  val = "8 word"
type_synonym memory = " addr \<Rightarrow> val"

definition char_to_ascii_nat :: "char \<Rightarrow> nat" where
  "char_to_ascii_nat c = of_char (String.ascii_of c)"

definition char_to_ascii_byte :: "char \<Rightarrow>val" where
  "char_to_ascii_byte c = of_nat (char_to_ascii_nat c)"

(*String  definition *)
definition string_in_memory :: "string \<Rightarrow> addr \<Rightarrow> memory \<Rightarrow> bool" where
  "string_in_memory x y mem \<equiv> \<forall>i < length x. char_to_ascii_byte (x ! i) = mem (y + of_nat i)"

definition read_byte :: "addr \<Rightarrow>  memory \<Rightarrow> val" where
  "read_byte a mem = mem a"

definition write_byte :: "addr  \<Rightarrow> val \<Rightarrow> memory \<Rightarrow>  memory" where
  "write_byte  a v mem = mem (a := v)"

(* Read/Write Bytes as inductive definitions *)


inductive  new_w_bytes :: " addr \<Rightarrow>  val list \<Rightarrow>  memory \<Rightarrow> memory\<Rightarrow> bool" where
  new_w_bytes0 :"new_w_bytes init_addr [] mem mem" |
  new_w_bytesL :"write_byte init_addr wrd mem = mem' \<Longrightarrow>
                 new_w_bytes (init_addr + 1) wlist mem' mem'' \<Longrightarrow>
                 new_w_bytes init_addr (wrd# wlist) mem' mem''"    

inductive new_r_bytes :: "addr \<Rightarrow> memory \<Rightarrow> val list \<Rightarrow> bool" where
  new_r_bytes0: "new_r_bytes init_addr mem []" |
  new_r_bytesL: "read_byte init_addr mem = v \<Longrightarrow>
                 new_r_bytes (init_addr +1) mem vlist \<Longrightarrow>
                 new_r_bytes init_addr mem (v#vlist)"

inductive r_bytes :: "addr \<Rightarrow> memory \<Rightarrow> val list \<Rightarrow> bool" where
  r_bytes0: "r_bytes init_addr mem []" |
  r_bytesL: "r_bytes (init_addr + 1) mem vlist \<Longrightarrow>
            r_bytes init_addr mem (read_byte init_addr mem # vlist)"

inductive  w_bytes :: " addr \<Rightarrow>  val list \<Rightarrow>  memory \<Rightarrow> memory\<Rightarrow> bool" where
  w_bytes0 :"w_bytes init_addr [] mem mem" |
  w_bytesL : "w_bytes (init_addr + 1)  wlist  (write_byte init_addr wrd mem) mem'\<Longrightarrow>
     w_bytes init_addr (wrd # wlist) mem mem'"

(* Read/Write Bytes as functions *)
fun write_bytes :: " addr \<Rightarrow>  val list \<Rightarrow>  memory \<Rightarrow>  memory" where
  "write_bytes init_addr [] mem = mem" |
  "write_bytes init_addr (wrd # wlist) mem =
     write_bytes (init_addr + 1) wlist (write_byte init_addr wrd mem)"

fun read_bytes :: "addr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory \<Rightarrow> val list" where
  "read_bytes init_addr str_length 0 mem = []" |
  "read_bytes init_addr str_length (Suc current_count) mem =
    (if current_count \<ge> str_length then []
     else read_byte init_addr mem # read_bytes (init_addr + 1) str_length current_count mem)"

datatype mem_op =  
      Read addr | 
      Write addr val |
      ReadBytes addr nat | 
      WriteBytes addr "val list"

(* memory operations *)
inductive eval_mem_op:: "memory \<Rightarrow> mem_op \<Rightarrow> memory \<Rightarrow>bool" where
  eval_read_byte: " eval_mem_op mem (Read a) mem"|
  eval_write_byte: " \<lbrakk> write_byte a v mem = mem' \<rbrakk>\<Longrightarrow> eval_mem_op mem (Write a v) mem'"|
  eval_read_bytes: "eval_mem_op mem (ReadBytes a n) mem"|
  eval_write_bytes:  "\<lbrakk> write_bytes a vlist mem = mem' \<rbrakk>  \<Longrightarrow> eval_mem_op mem (WriteBytes a vlist) mem'" 
end