import iconfig

open tactic

meta structure a_config :=
(max_iterations  : ℕ := 500)
(max_discovers   : ℕ := 0)
(suggest         : list pexpr := [])
(optimal         : bool := tt)
(exhaustive      : bool := ff)
(inflate_rws     : bool := ff)
(trace           : bool := ff)
(trace_summary   : bool := ff)
(trace_rules     : bool := ff)
(ssss   : string := "dd")

run_cmd (do
  iconfig.is_valid_config `a_config >>= trace
)

run_cmd (do
  e ← get_env,
  let n := `a_config,
  e.structure_fields n >>= list.mmap (iconfig.resolve_field e n),

  skip
)

meta instance : has_to_tactic_format a_config := ⟨λ b, return format!"{b.max_iterations} : {b.max_discovers}"⟩

section

iconfig_mk my_tac

iconfig_add_struct my_tac a_config

end

namespace tactic
namespace interactive

meta def cfgdump (c : iconfig my_tac) : tactic unit := do
  r ← iconfig.read c,
  r.struct `a_config a_config >>= tactic.trace,
  return ()

end interactive
end tactic

example : tt := begin
  cfgdump {
    max_iterations := 113,
    max_discovers := 112
  },

  simp
end
