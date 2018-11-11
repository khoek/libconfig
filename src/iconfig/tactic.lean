import .cfgopt

namespace iconfig

open tactic

meta inductive explained (α : Type)
| ok : α → explained
| bad : format → explained
open explained

meta def explained.unwrap {α : Type} : explained α → α → α
| (ok a) _    := a
| (bad _ _) a := a

meta def explained.force_unwrap {α : Type} : explained α → option α → tactic α
| (ok a) _            := return a
| (bad _ _) (some a)  := return a
| (bad _ reason) none := fail reason

def result := list cfgopt

namespace result

variable (r : result)

meta def to_list : list cfgopt := r

meta def dump : tactic unit :=
  tactic.trace r.to_list

private meta def find_aux (n : name) : list cfgopt → option cfgopt.value
| [] := none
| (⟨n', v⟩ :: rest) := if n = n' then v else find_aux rest

meta def find (n : name) : option cfgopt.value :=
find_aux n r.to_list

private meta def out_bad_type {α : Type} (n : name) : explained α :=
bad α format!"option '{n}' does not have type bool!"

private meta def out_bad_missing {α : Type} (n : name) : explained α :=
bad _ format!"option '{n}' not supplied!"

open cfgopt

meta def xbool (n : name) : explained bool :=
do match r.find n with
   | some c := match c with
               | value.bool v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def ibool (n : name) (default : bool) : bool :=
(xbool r n).unwrap default

meta def bool (n : name) (default : option bool := none) : tactic bool :=
(xbool r n).force_unwrap default

meta def xnat (n : name) : explained ℕ :=
do match r.find n with
   | some c := match c with
               | value.nat v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def inat (n : name) (default : nat) : nat :=
(xnat r n).unwrap default

meta def nat (n : name) (default : option nat := none) : tactic nat :=
(xnat r n).force_unwrap default

meta def xenat (n : name) : explained (with_top ℕ) :=
do match r.find n with
   | some c := match c with
               | value.enat v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def ienat (n : name) (default : with_top ℕ) : with_top ℕ :=
(xenat r n).unwrap default

meta def enat (n : name) (default : option (with_top ℕ) := none) : tactic (with_top ℕ) :=
(xenat r n).force_unwrap default

meta def xstring (n : name) : explained string :=
do match r.find n with
   | some c := match c with
               | value.string v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def istring (n : name) (default : string) : string :=
(xstring r n).unwrap default

meta def string (n : name) (default : option string := none) : tactic string :=
(xstring r n).force_unwrap default

meta def xident (n : name) : explained name :=
do match r.find n with
   | some c := match c with
               | value.name v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def iident (n : name) (default : name) : name :=
(xident r n).unwrap default

meta def ident (n : name) (default : option name := none) : tactic name :=
(xident r n).force_unwrap default

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

end iconfig
