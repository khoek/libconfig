import .result

namespace iconfig

open tactic

meta def publish (n : name) (co : cfgopt.value) : tactic unit := do
  g ← get_goal,
  m ← mk_meta_var `(list cfgopt),
  mk_app `list.cons [`(⟨n, co⟩ : cfgopt), m] >>= exact,
  set_goals [m]

private meta def collect (cfg : tactic unit) : tactic result := do
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
private meta def compile (r : result) : tactic result := do
  return r

meta def read (cfg : tactic unit) : tactic result := do
  collect cfg >>= compile

namespace tactic

open lean.parser interactive interactive.types
open cfgopt

meta def bool (n : name) (v : parse (letval pbool)) : tactic unit :=
  publish n $ value.bool v

meta def nat (n : name) (v : parse (letval small_nat)) : tactic unit :=
  publish n $ value.nat v

meta def enat (n : name) (v : parse (letval enat)) : tactic unit :=
  publish n $ value.enat v

meta def string (n : name) (v : parse (letval pstring)) : tactic unit :=
  publish n $ value.string v

meta def name (n : name) (v : parse ident) : tactic unit :=
  publish n $ value.name v

meta def pexpr (n : _root_.name) (v : parse texpr) : tactic unit :=
  publish n $ value.pexpr v

meta def list (t : type) (n : _root_.name) (v : parse lean.parser.pexpr) : tactic unit := do
  e ← to_expr v,
  publish n $ value.list t e

end tactic

end iconfig

namespace cfgopt.type

open cfgopt.type

meta def to_reader_pexpr : cfgopt.type → _root_.pexpr
| bool := ``(iconfig.tactic.bool)
| nat  := ``(iconfig.tactic.nat)
| enat  := ``(iconfig.tactic.enat)
| string := ``(iconfig.tactic.string)
| name := ``(iconfig.tactic.name)
| pexpr := ``(iconfig.tactic.pexpr)
| (list t) := ``(iconfig.tactic.list) $ pexpr.of_expr `(t)

end cfgopt.type
