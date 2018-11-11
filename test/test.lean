import config

open config

iconfig_mk my_tac

iconfig_add my_tac [
  abool  : config.boolc {},
  anum   : config.nat,
  aenum  : config.enat,
  astr   : config.string,
  aident : config.ident,
]

namespace tactic
namespace interactive

meta def cfgdump (c : iconfig my_tac) : tactic unit := do
  l ← config.read c,
  l.bool "abool" >>= tactic.trace,
  return ()

end interactive
end tactic

example : tt := begin
  cfgdump begin
    abool := ff,
    anum := 113,
    aenum := inf,
    astr := "ello",
    aident s.sss4,
  end,

  simp
end

