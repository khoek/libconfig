import .tactic

open iconfig
open tactic lean lean.parser
open interactive interactive.types

@[user_command] meta def iconfig_mk_cmd (_ : decl_meta_info) (_ : parse (tk "iconfig_mk")) : lean.parser unit := do
  n ← ident,
  of_tactic' $ iconfig.env_mk n

private meta def eat_members (cfgn : name) : lean.parser unit := (do
  n ← lean.parser.ident,
  lean.parser.tk ":",
  val ← lean.parser.ident,
  e ← mk_const $ (`iparam).append val,
  e ← eval_expr (name → name → lean.parser unit) e,
  e cfgn n,
  optional $ lean.parser.tk ",",
  eat_members)
  <|> return ()

@[user_command] meta def iconfig_add_cmd (_ : decl_meta_info) (_ : parse (tk "iconfig_add")) : lean.parser unit := do
  cfgn ← lean.parser.ident,
  assert_config_exists cfgn,
  lean.parser.tk "[",
  eat_members cfgn,
  lean.parser.tk "]"

@[user_command] meta def iconfig_add_struct_cmd (_ : decl_meta_info) (_ : parse (tk "iconfig_add_struct")) : lean.parser unit := do
  cfgn ← lean.parser.ident,
  assert_config_exists cfgn,
  struct ← lean.parser.ident,
  struct ← resolve_constant struct,
  iconfig.env_add_struct cfgn struct

reserve prefix iconfig:max
@[user_notation] meta def iconfig_not (_ : parse (tk "iconfig")) : lean.parser pexpr := do
  n ← lean.parser.ident,
  let e := ((`iconfig).append n).append `interactive.itactic,
  of_tactic' $ resolve_name e
