import .cfgopt

namespace config

open tactic

def result := list cfgopt

namespace result

variable (r : result)

meta def to_list : list cfgopt := r

private meta def find_aux (n : name) : list cfgopt → option cfgopt.value
| [] := none
| (⟨n', v⟩ :: rest) := if n = n' then v else find_aux rest

meta def find (n : name) : option cfgopt.value :=
find_aux n r.to_list

open cfgopt

private meta def out_bad_type {α : Type} (n : name) : tactic α :=
fail format!"option '{n}' does not have type bool!"

private meta def out_default {α : Type} (n : name) (default : option α) : tactic α :=
do match default with
   | none := fail format!"option '{n}' not specified!"
   | some a := return a
   end

meta def bool (n : name) (default : option bool := none) : tactic bool :=
do match r.find n with
   | some c := match c with
               | value.bool b := return b
               | _ := out_bad_type n
               end
   | none := out_default n default
   end

meta def nat (n : name) (default : option ℕ := none) : tactic ℕ :=
do match r.find n with
   | some c := match c with
               | value.nat v := return v
               | _ := out_bad_type n
               end
   | none := out_default n default
   end

meta def enat (n : name) (default : option (with_top ℕ) := none) : tactic (with_top ℕ) :=
do match r.find n with
   | some c := match c with
               | value.enat v := return v
               | _ := out_bad_type n
               end
   | none := out_default n default
   end

meta def string (n : name) (default : option string := none) : tactic string :=
do match r.find n with
   | some c := match c with
               | value.string s := return s
               | _ := out_bad_type n
               end
   | none := out_default n default
   end

meta def ident (n : name) (default : option name := none) : tactic name :=
do match r.find n with
   | some c := match c with
               | value.name v := return v
               | _ := out_bad_type n
               end
   | none := out_default n default
   end

meta def dump : tactic unit :=
  tactic.trace r.to_list

end result

meta def publish (n : name) (co : cfgopt.value) : tactic unit := do
  g ← get_goal,
  m ← mk_meta_var `(list cfgopt),
  mk_app `list.cons [`(⟨n, co⟩ : cfgopt), m] >>= exact,
  set_goals [m]

meta def collect (cfg : tactic unit) : tactic result := do
  gs ← get_goals,
  m ← mk_meta_var `(list cfgopt),
  set_goals [m],
  cfg,
  exact `(@list.nil cfgopt),
  l ← instantiate_mvars m,
  set_goals gs,
  eval_expr (list cfgopt) l

-- TODO Find duplicates, report a warning when they are overriding
-- or an error when they are of the wrong type.
meta def compile (r : result) : tactic result := do
  return r

meta def read (cfg : tactic unit) : tactic result := do
  collect cfg >>= compile

open lean.parser interactive interactive.types
open cfgopt

inductive overload_policy
| ignore
| override (n : option name) : overload_policy
| default (n : option name) : overload_policy

structure cfg_params (α : Type) :=
(default : option α := none)
(global_name : overload_policy := overload_policy.default none)

meta def boolc (cfg : cfg_params bool) (n : name) (v : parse (letval pbool)) : tactic unit :=
  publish n $ value.bool v

meta def bool (n : name) (v : parse (letval pbool)) : tactic unit :=
  boolc {} n v

meta def nat (n : name) (v : parse (letval small_nat)) : tactic unit :=
  publish n $ value.nat v

meta def enat (n : name) (v : parse (letval enat)) : tactic unit :=
  publish n $ value.enat v

meta def string (n : name) (v : parse (letval pstring)) : tactic unit :=
  publish n $ value.string v

meta def ident (n : name) (v : parse ident) : tactic unit :=
  publish n $ value.name v

end config
