import .cfgopt

meta def config (α : Type) :=
tactic α

meta instance : monad config :=
by dunfold config; apply_instance

meta instance : monad_fail config :=
by dunfold config; apply_instance

meta instance : alternative config :=
by dunfold config; apply_instance

namespace config

meta def save_info (p : pos) : config unit :=
do s ← tactic.read,
   tactic.save_info_thunk p (λ _, s.to_format tt)

meta def step {α : Type} (c : config α) : config unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : _root_.nat) (c : config α) : config unit :=
tactic.istep line0 col0 line col c

meta def execute (c : config unit) : tactic unit :=
c

end config
