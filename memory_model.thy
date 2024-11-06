section "Memory model for Smart Contract"

theory memory_model
  imports Main "Separation_Algebra.Separation_Algebra" "HOL-Library.Word" "HOL.String"
begin

type_synonym length = nat
type_synonym index = nat

datatype d_type = DChar |DShort| DInt
datatype ('a) val =  BlockAddr 'a | IntVal int | StringVal string

datatype ('a,'r) op =  
      ReadMemory 'a length | 
      WriteToMemory 'a "'r list"|
      ReadArray 'a index|
      WriteToArray 'a index "'r list"|
      ReadStruct 'a index|
      WriteToStruct 'a index "('a) val"|
      Skip

record ('a)struct_heap_block =
  st_size :: nat
  st_val_map :: "index \<Rightarrow> ('a) val"

record ('r) array_heap_block =
  size :: nat
  data_type :: d_type
  val_map :: "index \<Rightarrow> 'r"
                                                             
(* 'm- mem type, 'a- element addr, 'r- value  *)
locale memory_locale =   
   fixes mem :: "'m::sep_algebra"
   fixes read_from_mem :: "'m \<Rightarrow> 'a \<Rightarrow> 'r"
   fixes write_to_mem :: "'m \<Rightarrow> 'a \<Rightarrow> 'r \<Rightarrow>'m"
   fixes next_address :: "'a \<Rightarrow> 'a"
   fixes get_heap_block :: "'m \<Rightarrow> 'a \<Rightarrow> ('r) array_heap_block"
   fixes update_heap_block ::  "'m \<Rightarrow> 'a \<Rightarrow> ('r) array_heap_block \<Rightarrow>'m"
   fixes get_struct_heap_block :: "'m \<Rightarrow> 'a \<Rightarrow> ('a) struct_heap_block"
   fixes update_struct_heap_block ::  "'m \<Rightarrow> 'a \<Rightarrow> ('a) struct_heap_block \<Rightarrow>'m"
begin

inductive mem_access :: "'m * ('a,'r) op * 'r list \<Rightarrow> 'm * ('a,'r) op * 'r list\<Rightarrow> bool" (infix "\<rightarrow>" 55) where

  read_step:  "\<lbrakk> n > 0; b = read_from_mem mem a \<rbrakk> \<Longrightarrow>
               (mem, ReadMemory a n, r) \<rightarrow> (mem, ReadMemory (next_address a) (n-1), r @ [b])"|

  write_step: "\<lbrakk> mem' = write_to_mem mem a v\<rbrakk> \<Longrightarrow>(mem, WriteToMemory a (v#vl), r) \<rightarrow> (mem', WriteToMemory (next_address a) vl, r)"|

  read_array_step: "\<lbrakk>hb = get_heap_block mem a; idx < size hb; v = val_map hb idx \<rbrakk> \<Longrightarrow>
                    (mem, ReadArray a idx, r)\<rightarrow> (mem, Skip, r@[v])"|

  write_array_step: "\<lbrakk>hb = get_heap_block mem a; idx < size hb; hb' = hb\<lparr> val_map := (val_map hb)(idx := v)\<rparr>;
                      mem' = update_heap_block mem a hb'\<rbrakk> \<Longrightarrow>
                     (mem, WriteToArray a idx (v#vl), r)\<rightarrow> (mem', WriteToArray  (next_address a) (idx+1) vl, r)"
  
end

end
                 