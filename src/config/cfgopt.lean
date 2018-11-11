import .lib

namespace cfgopt
@[derive has_reflect]
inductive value
| bool   : bool → value
| nat    : ℕ → value
| enat   : with_top ℕ → value
| string : string → value
| name   : name → value
open value

instance value.has_to_string : has_to_string value := ⟨λ v,
match v with
| bool b := sformat!"{b}:bool"
| nat n := sformat!"{n}:ℕ"
| enat none := sformat!"∞:eℕ"
| enat (some n) := sformat!"{n}:eℕ"
| string s := sformat!"{s}:string"
| name n := sformat!"{n}:name"
end ⟩
end cfgopt

@[derive has_reflect]
structure cfgopt :=
(key : name)
(val : cfgopt.value)
namespace cfgopt

instance has_to_string : has_to_string cfgopt :=
⟨λ v, sformat!"{v.key}={v.val}"⟩
meta instance has_to_tactic_format : has_to_tactic_format cfgopt :=
⟨λ v, return $ to_string v⟩

end cfgopt
