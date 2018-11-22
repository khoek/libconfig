import .cfgopt

meta def cfgtactic (α : Type) :=
tactic α

meta instance : monad cfgtactic :=
by dunfold cfgtactic; apply_instance

meta instance : monad_fail cfgtactic :=
by dunfold cfgtactic; apply_instance

meta instance : alternative cfgtactic :=
by dunfold cfgtactic; apply_instance

namespace iconfig

def INTERNAL_INST_NAME : name := `__internal_inst

meta def publish_core (n : name) (co : cfgopt.value) : tactic unit := do
  m ← tactic.mk_meta_var `(list cfgopt),
  tactic.mk_app `list.cons [`(⟨n, co⟩ : cfgopt), m] >>= tactic.exact,
  tactic.set_goals [m]

meta def publish (n : name) (co : cfgopt.value) : tactic unit :=
  get_goal >> publish_core n co

private meta def publish_inst_name (cfgn : name) : tactic unit :=
  publish_core INTERNAL_INST_NAME $ cfgopt.value.name cfgn

private meta def save_name (cfgn : name) : tactic unit := do
  gs ← tactic.get_goals,
  if gs.length = 2 then do
    tactic.set_goals (gs.nth 0).to_list,
    publish_inst_name cfgn
  else tactic.skip

meta def save_info (cfgn : name) (p : pos) : cfgtactic unit :=
do save_name cfgn,
   s ← tactic.read,
   tactic.save_info_thunk p (λ _, s.to_format tt)

meta def step {α : Type} (c : cfgtactic α) : cfgtactic unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : _root_.nat) (c : cfgtactic α) : cfgtactic unit :=
tactic.istep line0 col0 line col c

meta def execute (tac : cfgtactic unit) : tactic unit := tac

meta def pass (cfgn : name) : cfgtactic unit := save_name cfgn

end iconfig
