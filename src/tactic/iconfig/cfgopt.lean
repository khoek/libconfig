import .lib

namespace cfgopt

@[derive [has_reflect, decidable_eq]]
inductive type
| bool
| nat
| enat
| string
| name
| pexpr
| list (t : type)

namespace type

meta def to_pexpr : type → _root_.pexpr
| bool := ``(_root_.bool)
| nat  := ``(_root_.nat)
| enat  := ``(with_top ℕ)
| string := ``(_root_.string)
| name := ``(_root_.name)
| pexpr := ``(_root_.pexpr)
| (list t) := ``(_root_.list) t.to_pexpr

meta def to_Type : type → Type
| bool := _root_.bool
| nat  := _root_.nat
| enat  := with_top ℕ
| string := _root_.string
| name := _root_.name
| pexpr := _root_.pexpr
| (list t) := _root_.list t.to_Type

meta mutual def from_expr, get_list_type
with from_expr : expr → option type | e :=
  if e = `(_root_.bool)   then type.bool   else
  if e = `(_root_.nat)    then type.nat    else
  if e = `(_root_.string) then type.string else
  if e = `(_root_.name)   then type.name   else
  if e = `(_root_.pexpr)  then type.pexpr  else
  match get_list_type e with
  | some t := type.list t
  | none   := none
  end
with get_list_type : expr → option type | e :=
  if e.app_fn.const_name = `list then from_expr e.app_arg
  else none

def to_string : type → _root_.string
| bool := "bool"
| nat  := "ℕ"
| enat  := "eℕ"
| string := "string"
| name := "name"
| pexpr := "pexpr"
| (list t) := "(list " ++ t.to_string ++ ")"

instance : has_to_string type := ⟨type.to_string⟩
meta instance : has_to_format type := ⟨format.of_string ∘ type.to_string⟩

end type

@[derive has_reflect]
meta inductive value
| bool   : bool → value
| nat    : ℕ → value
| enat   : with_top ℕ → value
| string : string → value
| name   : name → value
| pexpr  : pexpr → value
| list   : type → expr → value
open value

namespace value

meta def to_type : value → type
| (bool _) := type.bool
| (nat _) := type.nat
| (enat _) := type.enat
| (string _) := type.string
| (name _) := type.name
| (pexpr _) := type.pexpr
| (list t _) := type.list t

meta def to_Type : value → Type := type.to_Type ∘ to_type

meta def to_expr : value → expr
| (bool b) := `(b)
| (nat n) := `(n)
| (enat e) := `(e)
| (string s) := `(s)
| (name n) := `(n)
| (pexpr p) := `(p)
| (list _ l) := l

meta def to_value_string : value → _root_.string
| (bool b) := sformat!"{b}"
| (nat n) := sformat!"{n}"
| (enat none) := sformat!"∞"
| (enat (some n)) := sformat!"{n}"
| (string s) := sformat!"{s}"
| (name n) := sformat!"{n}"
| (pexpr p) := sformat!"{p}"
| (list _ l) := sformat!"{l}"

meta def to_string (v : value) : _root_.string :=
sformat!"{v.to_value_string}:{v.to_type}"

meta instance has_to_string : has_to_string value := ⟨to_string⟩

end value

end cfgopt

@[derive has_reflect]
meta structure cfgopt :=
(key : name)
(val : cfgopt.value)
namespace cfgopt

meta instance has_to_string : has_to_string cfgopt :=
⟨λ v, sformat!"{v.key}={v.val}"⟩
meta instance has_to_tactic_format : has_to_tactic_format cfgopt :=
⟨λ v, return $ to_string v⟩

end cfgopt
