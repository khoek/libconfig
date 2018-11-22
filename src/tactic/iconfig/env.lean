import .monad
import .struct

namespace iconfig

open tactic

meta def mk_config_ns (cfgn : name) : name := (`iconfig).append cfgn

meta def assert_config_exists (cfgn : name) : tactic unit := do
  e ← get_env,
  if e.is_namespace $ mk_config_ns cfgn then skip
  else fail format!"There is no config `{cfgn}`"

private meta def make_ns_defs (ns : name) : list (name × expr × expr) → tactic unit
| [] := return ()
| ((s, t, v) :: rest) := do
  add_decl $ declaration.defn (ns.append s) [] t v (reducibility_hints.regular 1 tt) ff,
  make_ns_defs rest

private meta def name_to_schema (n : name) : tactic schema :=
  resolve_name n >>= to_expr >>= eval_expr schema
  <|> fail format!"'{n}' is not of type 'schema'!"

private meta def attr_after_set (decl : name) (prio : nat) (persistent : bool) : tactic unit :=
  name_to_schema decl >> skip

meta def env_mk (cfgn : name) : tactic unit := do
  let pfx := mk_config_ns cfgn,
  e ← get_env,
  set_env $ e.add_namespace pfx,
  make_ns_defs pfx [
    (`save_info, `(pos → cfgtactic unit), `(iconfig.save_info cfgn)),
    (`step, `(Π {α : Type}, cfgtactic α → cfgtactic unit), `(λ {α : Type} (c : cfgtactic α), iconfig.step c)),
    (`execute, `(cfgtactic unit → tactic unit), `(iconfig.execute)),
    (`interactive.itactic, `(Type), `(cfgtactic unit)),
    (`attr, `(user_attribute), `({user_attribute . name := (`iconfig_schema).append cfgn, descr := "iconfig schema", after_set := attr_after_set}))
  ],
  attribute.register (pfx.append `attr),

  it ← mk_const $ pfx.append `interactive.itactic,
  e ← mk_app `has_emptyc [it],
  make_ns_defs pfx [
    (`interactive.itactic.has_emptyc, e, `(has_emptyc.mk $ iconfig.pass cfgn))
  ],
  set_basic_attribute `instance (pfx.append `interactive.itactic.has_emptyc) tt

meta def env_add_schema (cfgn : name) (n : name) (s : schema) : tactic unit := do
  let pfx := mk_config_ns cfgn,
  make_ns_defs pfx [
    ((`attr).append n, `(schema), `(s))
  ],
  attr ← resolve_name (pfx.append `attr) >>= to_expr >>= eval_expr user_attribute,
  attr.set ((pfx.append (`attr)).append n) () tt

private def get_suffix : name → name
| name.anonymous        := name.anonymous
| (name.mk_string s p)  := s
| (name.mk_numeral s p) := to_string s

meta def env_get_schema (cfgn : name) : tactic (list (name × schema)) := do
  l ← attribute.get_instances ((`iconfig_schema).append cfgn),
  l.mmap $ λ n, do s ← name_to_schema n, return (get_suffix n, s)

meta def env_add (cfgn : name) (n : name) (val : pexpr) : tactic unit := do
  val ← to_expr val,
  let val := expr.app val `(n),
  ty ← infer_type val,

  make_ns_defs (mk_config_ns cfgn) [
    ((`interactive).append n, ty, val)
  ]

end iconfig
