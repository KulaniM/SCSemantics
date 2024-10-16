section "Memory model for Smart Contract"

theory memory_model_9_small_step imports Main  "HOL-Library.Word" HOL.String  begin

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
      ReadNextBytes addr nat "val list" | 
      WriteBytes addr "val list"|
      WriteNextBytes addr "val list"|
      Done result

inductive small_step_mem_op:: "mem_op * memory \<Rightarrow>  mem_op * memory \<Rightarrow> bool"(infix "\<rightarrow>" 55) where

  (* read/write a single byte *)
  read_byte: "\<lbrakk> read_byte a mem = v \<rbrakk>\<Longrightarrow> (Read a, mem) \<rightarrow> (Done[v], mem)"|

  write_byte:"\<lbrakk> write_byte a v mem = mem' \<rbrakk>\<Longrightarrow> (Write a v, mem) \<rightarrow> (Done[], mem')"|

  (* write a sequence of bytes *)
  write_bytes_init: "\<lbrakk> write_byte a v mem = mem'\<rbrakk> \<Longrightarrow>
                      (WriteBytes a (v#vl), mem)\<rightarrow> (WriteNextBytes (a + 1) vl , mem')"|
  write_bytes_next: "\<lbrakk> write_byte a v mem = mem''\<rbrakk> \<Longrightarrow>
                      (WriteNextBytes a (v#vl), mem')\<rightarrow> (WriteNextBytes (a + 1) vl , mem'')"|
  write_bytes_done: "(WriteNextBytes a [], mem)\<rightarrow> (Done[] , mem)"|

  (* read a sequence of bytes *)
  read_bytes_init: "\<lbrakk> n > 0; read_byte a mem = v \<rbrakk> \<Longrightarrow>
                      (ReadBytes a n, mem) \<rightarrow> (ReadNextBytes (a + 1) (n-1) [v], mem)"|
  read_bytes_next: "\<lbrakk> n > 0; read_byte a mem = v \<rbrakk> \<Longrightarrow>
                      (ReadNextBytes a n vl, mem) \<rightarrow> (ReadNextBytes (a + 1) (n-1) (vl@[v]), mem)"|
  read_bytes_done: "(ReadNextBytes a 0 vl, mem) \<rightarrow> (Done vl, mem)"

end