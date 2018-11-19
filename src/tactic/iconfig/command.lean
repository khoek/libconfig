import .lib.parser
import .monad
import .struct
import .tactic

open lean lean.parser
open interactive interactive.types

meta def mk_config_ns (n : name) : name := (`config).append n

private meta def make_ns_defs (ns : name) : environment → list (name × expr × expr) → tactic environment
| e [] := return e
| e ((s, t, v) :: rest) := do
  e ← e.add $ declaration.defn (ns.append s) [] t v (reducibility_hints.regular 1 tt) ff,
  make_ns_defs e rest

meta def iconfig_mk (n : name) : tactic unit := do
  e ← tactic.get_env,
  e ← make_ns_defs (mk_config_ns n) e [
    (`save_info, `(pos → iconfig_tac unit), `(iconfig.save_info)),
    (`step, `(Π {α : Type}, iconfig_tac α → iconfig_tac unit), `(λ {α : Type} (c : iconfig_tac α), iconfig.step c)),
    (`interactive.itactic, `(Type), `(iconfig_tac unit))
  ],
  tactic.set_env e

meta def iconfig_add (cfgn : name) (n : name) (val : pexpr) : tactic unit := do
  val ← tactic.to_expr val,
  let val := expr.app val `(n),
  ty ← tactic.infer_type val,

  e ← tactic.get_env,
  e ← make_ns_defs (mk_config_ns cfgn) e [
    ((`interactive).append n, ty, val)
  ],
  tactic.set_env e

meta def iconfig_add_struct (cfgn : name) (struct : name) : tactic unit := do
  e ← tactic.get_env,
  l ← iconfig.get_struct_types e struct,
  l.mmap' (λ s, iconfig_add cfgn s.1 s.2.to_reader_pexpr)

@[user_command] meta def iconfig_mk_cmd (meta_info : decl_meta_info) (_ : parse (tk "iconfig_mk")) : lean.parser unit := do
  n ← ident,
  of_tactic' $ iconfig_mk n

private meta def eat_pairs (cfgn : name) : lean.parser unit := (do
  n ← lean.parser.ident,
  lean.parser.tk ":",
  val ← texpr,
  of_tactic' $ iconfig_add cfgn n val,
  optional $ lean.parser.tk ",",
  eat_pairs
) <|> return ()

@[user_command] meta def iconfig_add_cmd (meta_info : decl_meta_info) (_ : parse (tk "iconfig_add")) : lean.parser unit := do
  cfgn ← lean.parser.ident,
  lean.parser.tk "[",
  eat_pairs cfgn,
  lean.parser.tk "]"

@[user_command] meta def iconfig_add_struct_cmd (meta_info : decl_meta_info) (_ : parse (tk "iconfig_add_struct")) : lean.parser unit := do
  cfgn ← lean.parser.ident,
  struct ← lean.parser.ident,
  iconfig_add_struct cfgn struct

reserve prefix iconfig:max
@[user_notation] meta def iconfig_not (_ : parse (tk "iconfig")) : lean.parser pexpr := do
  n ← lean.parser.ident,
  let e := ((`config).append n).append `interactive.itactic,
  of_tactic' $ tactic.resolve_name e
