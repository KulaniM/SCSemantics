section "Memory model for Smart Contract"

theory memory_model_5 imports Main  "HOL-Library.Word" HOL.String  begin

type_synonym 'a addr = "'a word"
type_synonym 'b val = "'b word"
type_synonym ('a, 'b) memory = "'a addr \<Rightarrow> 'b val"
type_synonym str_len = nat
type_synonym count = nat

definition read_word :: "'a addr \<Rightarrow> ('a, 'b) memory \<Rightarrow> 'b val" where
  "read_word a mem = mem a"

definition write_word :: "'a addr  \<Rightarrow> 'b val \<Rightarrow> ('a, 'b) memory \<Rightarrow> ('a, 'b) memory" where
  "write_word  a v mem = mem (a := v)"

fun write_word_list :: "('a::len) addr \<Rightarrow> 'b word list \<Rightarrow> ('a, 'b) memory \<Rightarrow> ('a, 'b) memory" where
  "write_word_list init_addr [] mem = mem" |
  "write_word_list init_addr (wrd # wlist) mem =
     write_word_list (init_addr + 8) wlist (write_word init_addr wrd mem)"

fun read_word_list :: "('a::len) addr \<Rightarrow> str_len \<Rightarrow> count \<Rightarrow> ('a, 'b) memory \<Rightarrow> 'b word list" where
  "read_word_list init_addr str_length 0 mem = []" |
  "read_word_list init_addr str_length (Suc current_count) mem =
    (if current_count \<ge> str_length then []
     else read_word init_addr mem # read_word_list (init_addr + 8) str_length current_count mem)"
end