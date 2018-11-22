import data.list
import .types
import .schema
import .monad
import .env

namespace iconfig

meta inductive explained (α : Type)
| ok : α → explained
| bad : format → explained
open explained

meta def explained.to_option {α : Type} : explained α → option α
| (ok a)    := some a
| (bad _ _) := none

meta def explained.unwrap {α : Type} : explained α → α → α
| (ok a) _    := a
| (bad _ _) a := a

meta def explained.munwrap {α : Type} : explained α → option α → tactic α
| (ok a) _            := return a
| (bad _ _) (some a)  := return a
| (bad _ reason) none := tactic.fail reason

namespace result

variable (r : result)

meta def dump : tactic unit :=
  tactic.trace r.opts

private meta def cfgopt_find (n : name) : list cfgopt → option cfgopt.value
| [] := none
| (⟨n', v⟩ :: rest) := if n = n' then v else cfgopt_find rest

private meta def schema_find (n : name) : list (name × schema) → option schema
| [] := none
| ((n', s) :: rest) := if n = n' then s else schema_find rest

meta def find (n : name) : option cfgopt.value :=
let s := match schema_find n r.sch with
| none := default_schema
| some s := s
end in s.apply $ cfgopt_find n r.opts

meta def clear (n : name) : result :=
  {r with opts := r.opts.filter $ λ co, co.key ≠ n}

meta def clearl : result → list name → result
| r [] := r
| r (n :: rest) := clearl (r.clear n) rest

meta def add (n : name) (v : cfgopt.value) : result :=
  {r with opts := r.opts.concat ⟨n, v⟩}

meta def addl : result → list (name × cfgopt.value) → result
| r [] := r
| r ((n, v) :: rest) := addl (r.add n v) rest

meta def set (n : name) (v : cfgopt.value) : result :=
  (r.clear n).add n v

meta def setl : result → list (name × cfgopt.value) → result
| r [] := r
| r ((n, v) :: rest) := setl (r.set n v) rest

end result

namespace result

private meta def out_bad_type {α : Type} (n : name) : explained α :=
bad _ format!"option '{n}' does not have type bool!"

private meta def out_bad_missing {α : Type} (n : name) : explained α :=
bad _ format!"option '{n}' not supplied!"

open cfgopt

variable (r : result)

meta def xbool (n : name) : explained bool :=
do match r.find n with
   | some c := match c with
               | value.bool v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def obool (n : name) : option bool :=
(xbool r n).to_option

meta def ibool (n : name) (default : bool) : bool :=
(xbool r n).unwrap default

meta def bool (n : name) (default : option bool := none) : tactic bool :=
(xbool r n).munwrap default

meta def xnat (n : name) : explained ℕ :=
do match r.find n with
   | some c := match c with
               | value.nat v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def onat (n : name) : option nat :=
(xnat r n).to_option

meta def inat (n : name) (default : nat) : nat :=
(xnat r n).unwrap default

meta def nat (n : name) (default : option nat := none) : tactic nat :=
(xnat r n).munwrap default

meta def xenat (n : name) : explained (with_top ℕ) :=
do match r.find n with
   | some c := match c with
               | value.enat v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def oenat (n : name) : option (with_top ℕ) :=
(xenat r n).to_option

meta def ienat (n : name) (default : with_top ℕ) : with_top ℕ :=
(xenat r n).unwrap default

meta def enat (n : name) (default : option (with_top ℕ) := none) : tactic (with_top ℕ) :=
(xenat r n).munwrap default

meta def xstring (n : name) : explained string :=
do match r.find n with
   | some c := match c with
               | value.string v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def ostring (n : name) : option string :=
(xstring r n).to_option

meta def istring (n : name) (default : string) : string :=
(xstring r n).unwrap default

meta def string (n : name) (default : option string := none) : tactic string :=
(xstring r n).munwrap default

meta def xname (n : name) : explained name :=
do match r.find n with
   | some c := match c with
               | value.name v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def oname (n : name) : option name :=
(xname r n).to_option

meta def iname (n : name) (default : name) : name :=
(xname r n).unwrap default

meta def name (n : name) (default : option name := none) : tactic name :=
(xname r n).munwrap default

meta def xpexpr (n : _root_.name) : explained pexpr :=
do match r.find n with
   | some c := match c with
               | value.pexpr v := ok v
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def opexpr (n : _root_.name) : option pexpr :=
(xpexpr r n).to_option

meta def ipexpr (n : _root_.name) (default : pexpr) : pexpr :=
(xpexpr r n).unwrap default

meta def pexpr (n : _root_.name) (default : option pexpr := none) : tactic pexpr :=
(xpexpr r n).munwrap default

meta def xlist_raw (t : type) (n : _root_.name) : explained expr :=
do match r.find n with
   | some c := match c with
               | value.list t' v :=
                 if t = t' then ok v
                 else bad _ format!"type of list '{n}' should be {t}, but instead is {t'}!"
               | _ := out_bad_type n
               end
   | none := out_bad_missing n
   end

meta def olist_raw (t : type) (n : _root_.name) : option expr :=
(xlist_raw r t n).to_option

meta def list_raw (t : type) (n : _root_.name) (default : option expr := none) : tactic expr :=
(xlist_raw r t n).munwrap default

-- meta def olist (α : Type) (n : _root_.name) : option (list α) :=
-- let r := r in sorry

-- meta def list (α : Type) (n : _root_.name) : tactic (list α) :=
-- let r := r in sorry

end result

namespace result

open cfgopt

variable (r : result)

meta def olookup (n : _root_.name) : type → option value
| type.bool := value.bool <$> r.obool n
| type.nat := value.nat <$> r.onat n
| type.enat := value.enat <$> r.oenat n
| type.string := value.string <$> r.ostring n
| type.name := value.name <$> r.oname n
| type.pexpr := value.pexpr <$> r.opexpr n
| (type.list t) := value.list t <$> r.olist_raw t n

meta def lookup (n : _root_.name) : type → tactic value
| type.bool := value.bool <$> r.bool n
| type.nat := value.nat <$> r.nat n
| type.enat := value.enat <$> r.enat n
| type.string := value.string <$> r.string n
| type.name := value.name <$> r.name n
| type.pexpr := value.pexpr <$> r.pexpr n
| (type.list t) := value.list t <$> r.list_raw t n

open tactic

meta def struct (r : result) (n : _root_.name) (α : Type) [reflected α] : tactic α := do
  e ← get_env,
  n ← resolve_constant n,
  fs ← get_struct_types e n,
  mk_config n α $ list.join $ fs.map (λ s,
    match r.olookup s.1 s.2 with
    | some v := [(s.1, v)]
    | none := []
    end
  )

end result

open tactic

private meta def collect (cfg : tactic unit) : tactic (list cfgopt) := do
  gs ← get_goals,
  m₁ ← mk_meta_var `(list cfgopt),
  m₂ ← mk_meta_var `(unit),
  set_goals [m₁, m₂],
  cfg,
  exact `(@list.nil cfgopt),
  l ← instantiate_mvars m₁,
  set_goals gs,
  eval_expr (list cfgopt) l

-- TODO Find duplicates, report a warning when they are overriding
-- or an error when they are of the wrong type.
private meta def compile (r : list cfgopt) : tactic (list cfgopt) :=
  return r

meta def read (cfg : tactic unit) : tactic result := do
  opts ← collect cfg >>= compile,
  cfgn ← (⟨opts, []⟩ : result).name INTERNAL_INST_NAME,
  sch ← env_get_schema cfgn,
  return ⟨opts, sch⟩

end iconfig
