section "Memory model for Smart Contract"

theory memory_model_10_ss_dtype imports Main  "HOL-Library.Word" HOL.String  begin

type_synonym  addr = "32 word"
type_synonym  byte = "8 word"
type_synonym memory = " addr \<Rightarrow> byte"
type_synonym result = "byte list"
type_synonym bit_stream = "bool list"

datatype d_type = DChar |DShort| DInt

(* Converts a list of bits to a word) *)
definition bits_to_word :: "bool list \<Rightarrow> 'a::len word" where
  "bits_to_word bits = word_of_int (foldr (\<lambda>b acc. acc * 2 + (if b then 1 else 0)) bits 0)"

(* Determine no of bytes (8 word) based on data type: for data read *)
fun find_bytes_size :: "d_type \<Rightarrow> nat" where
  "find_bytes_size DChar = 1"|
  "find_bytes_size DShort = 2"|
  "find_bytes_size DInt = 4"

(*Convert the bitstream to a byte list for data writing using WriteBytes*)
(* fun data_to_byte_list :: "bit_stream \<Rightarrow> d_type \<Rightarrow> byte list" where*)


(*Read/write byte  definitions *)
definition read_byte :: "addr \<Rightarrow>  memory \<Rightarrow> byte" where
  "read_byte a mem = mem a"
definition write_byte :: "addr  \<Rightarrow> byte \<Rightarrow> memory \<Rightarrow>  memory" where
  "write_byte  a v mem = mem (a := v)"

(* memory operations *)
datatype mem_op =  
      Read addr | 
      Write addr byte |
      ReadBytes addr nat | 
      ReadNextBytes addr nat "byte list" | 
      WriteBytes addr "byte list"|
      WriteNextBytes addr "byte list"|
      Done result|
      ReadData addr d_type|
      WriteData addr d_type bit_stream

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
  read_bytes_done: "(ReadNextBytes a 0 vl, mem) \<rightarrow> (Done vl, mem)"|

  (* read/write data of a given primitive type *)
  read__data_init:  "\<lbrakk> find_bytes_size dt = n\<rbrakk> \<Longrightarrow>
                      (ReadData a dt, mem)\<rightarrow> (ReadBytes a n, mem)"

  (* write__data_init:  "\<lbrakk> data_to_byte_list bs dt = vl\<rbrakk> \<Longrightarrow>
                      (WriteData a dt bs , mem)\<rightarrow> (WriteBytes a vl, mem)"*)

end