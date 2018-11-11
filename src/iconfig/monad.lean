import .cfgopt

meta def iconfig_tac (α : Type) :=
tactic α

meta instance : monad iconfig_tac :=
by dunfold iconfig_tac; apply_instance

meta instance : monad_fail iconfig_tac :=
by dunfold iconfig_tac; apply_instance

meta instance : alternative iconfig_tac :=
by dunfold iconfig_tac; apply_instance

namespace iconfig

meta def save_info (p : pos) : iconfig_tac unit :=
do s ← tactic.read,
   tactic.save_info_thunk p (λ _, s.to_format tt)

meta def step {α : Type} (c : iconfig_tac α) : iconfig_tac unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : _root_.nat) (c : iconfig_tac α) : iconfig_tac unit :=
tactic.istep line0 col0 line col c

meta def execute (c : iconfig_tac unit) : tactic unit :=
c

end iconfig
