import tactic.iconfig

section

iconfig_mk my_tac

iconfig_add my_tac [
  abool  : iconfig.bool,
  anum   : iconfig.nat,
  aenum  : iconfig.enat,
  astr   : iconfig.string,
  aident : iconfig.ident,
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

