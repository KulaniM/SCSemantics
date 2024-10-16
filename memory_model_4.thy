section "Memory model for Smart Contract"

theory memory_model_4 imports Main  "HOL-Library.Word" HOL.String  begin

type_synonym word8 = "8 word"
type_synonym word32 = "32 word"
datatype  val = Word32_Val word32 |  Word8_Val word8
type_synonym addr = word32
type_synonym memory = "addr \<Rightarrow> val"
type_synonym string = "char list"
  
definition read_word32 :: "addr \<Rightarrow> memory => val" where
 "read_word32 a mem = mem a "

definition write_word32 :: "addr \<Rightarrow> val \<Rightarrow> memory => memory" where
 "write_word32 a v mem = mem (a := v) "

definition read_word8 :: "addr \<Rightarrow> memory => val" where
 "read_word8 a mem = mem a "

definition write_word8 :: "addr \<Rightarrow> val \<Rightarrow> memory => memory" where
 "write_word8 a v mem = mem (a := v) "

definition char_to_ascii_nat :: "char \<Rightarrow> nat" where
  "char_to_ascii_nat c = of_char (String.ascii_of c)"

definition char_to_ascii_word8 :: "char \<Rightarrow> word8" where
  "char_to_ascii_word8 c = of_nat (char_to_ascii_nat c)"

function write_char_list :: "addr \<Rightarrow> char list \<Rightarrow> memory \<Rightarrow> memory" where
  "write_char_list init_addr [] mem = mem"|
  "write_char_list init_addr (c # clist) mem =
                write_char_list (init_addr + 1) clist (write_word8 init_addr 
                (Word8_Val(char_to_ascii_word8 c)) mem)"

definition write_string :: "addr \<Rightarrow> string \<Rightarrow> lengh \<Rightarrow> memory \<Rightarrow> memory" where
  "write_string init_addr str l mem =  "













end