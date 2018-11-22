import tactic.iconfig

section

iconfig_mk my_tac

set_option formatter.hide_full_terms false

iconfig_add my_tac [
  abool  : bool, -- (TODO:) := tt ! iconfig.overload_policy.ignore⟩,
  anum   : nat,
  aenum  : enat,
  astr   : string,
  aident : name,
]

end

namespace tactic
namespace interactive

meta def cfgdump (c : iconfig my_tac) : tactic unit := do
  l ← iconfig.read c,
  l.bool "abool" >>= tactic.trace,
  return ()

end interactive
end tactic

example : tt := begin
  cfgdump {
    abool := ff,
    anum := 113,
    aenum := inf,
    astr := "ello",
    aident s.sss4,
  },

  simp
end

