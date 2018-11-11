open tactic

meta def get_goal : tactic expr := do
  gs ← get_goals,
  match gs with
  | [a] := return a
  | []  := fail "error, there are no goals"
  | _   := fail "error, there are too many goals"
  end
