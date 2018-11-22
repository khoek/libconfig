import .types

namespace iconfig

open tactic cfgopt

meta def is_valid_config (n : name) : tactic bool :=
  (to_expr $ pexpr.mk_structure_instance ⟨some n, [], [], []⟩) >> return tt
  <|> return ff

meta def assert_valid_config (n : name) : tactic unit := do
  r ← is_valid_config n,
  if r then skip else fail format!"config '{n}' cannot be instantiated as '{{}'"

meta def resolve_field (e : environment) (struct : name) (field : name) : tactic expr := do
  e ← mk_const (struct.append field) >>= infer_type,
  match e with
    | expr.pi _ _ _ t := pure t
    | _ := fail "read invalid expr"
  end

meta def get_struct_types (e : environment) (struct : name) : tactic (list (name × type)) := do
  assert_valid_config struct,
  e.structure_fields struct >>= list.mmap (λ s, do r ← type.from_expr <$> resolve_field e struct s, r ← r, return (s, r))

meta def mk_config (struct : name) (α : Type) [reflected α] (fields : list (name × value)) : tactic α :=
  (to_expr $ pexpr.mk_structure_instance ⟨some struct, fields.map prod.fst, fields.map (λ s, pexpr.of_expr s.2.to_expr), []⟩) >>= eval_expr α

end iconfig
