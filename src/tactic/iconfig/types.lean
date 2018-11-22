import .cfgopt

namespace iconfig

@[derive has_reflect]
inductive overload_policy
| ignore
| override (n : option name) : overload_policy
| default (n : option name) : overload_policy

@[derive has_reflect]
meta structure schema :=
(default : option cfgopt.value := none)
(overload : overload_policy := overload_policy.default none)

@[derive has_reflect]
meta structure result :=
(opts : list cfgopt)
(sch : list (name × schema))

meta def empty_result : result := ⟨[], []⟩

end iconfig
