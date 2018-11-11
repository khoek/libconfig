import order.bounded_lattice

open lean lean.parser
open interactive interactive.types
open tactic

namespace interactive.types

private meta def bool_from_pexpr : pexpr → lean.parser bool
| (expr.local_const `tt `tt _ _) := return tt
| (expr.local_const `ff `ff _ _) := return ff
| e := interaction_monad.fail format!"'{e}' not a bool"

meta def pbool : parser bool := lean.parser.pexpr >>= bool_from_pexpr

private meta def string_from_pexpr (pe : pexpr) : lean.parser string :=
of_tactic' $ to_expr pe >>= eval_expr string

meta def pstring : parser string := lean.parser.pexpr >>= string_from_pexpr

private meta def enat_from_name (n : name) : lean.parser (with_top ℕ) :=
if n = `inf ∨ n = `infty ∨ n = `infinity ∨ n = `none then return none
else interaction_monad.fail "not infinity!"

meta def enat : parser (with_top ℕ) := (some <$> small_nat)
  <|> (ident >>= enat_from_name)
  <|> interaction_monad.fail "not an extended natural!"

reserve prefix `:=`:max
meta def letval {α : Type} (p : lean.parser α) := tk ":=" *> p

end interactive.types
