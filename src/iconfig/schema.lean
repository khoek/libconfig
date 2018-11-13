
namespace iconfig

inductive overload_policy
| ignore
| override (n : option name) : overload_policy
| default (n : option name) : overload_policy

structure schema_item (α : Type) :=
(default : option α := none)
(global_name : overload_policy := overload_policy.default none)

end iconfig
