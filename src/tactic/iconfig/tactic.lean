import .types
import .monad
import .env

namespace iparam

namespace handler

open lean.parser interactive interactive.types
open iconfig cfgopt

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

meta def lpexpr (n : _root_.name) (v : parse (letval texpr)) : tactic unit :=
  publish n $ value.pexpr v

meta def pexpr (n : _root_.name) (v : parse texpr) : tactic unit :=
  publish n $ value.pexpr v

meta def list (t : type) (n : _root_.name) (v : parse (letval lean.parser.pexpr)) : tactic unit := do
  e ← tactic.to_expr v,
  publish n $ value.list t e

end handler

open iconfig tactic
open lean.parser interactive interactive.types

private meta def handle_member (cfgn : name) (n : name) (val : pexpr) (default : option pexpr) : tactic unit := do
  iconfig.env_add cfgn n val,
  match default with
  | none := tactic.skip
  | some default :=
    to_expr default >>= eval_expr schema >>= env_add_schema cfgn n
  end

meta def generic (val : pexpr) (cfgn : name) (n : name) : lean.parser unit := do
  default_present ← optional $ lean.parser.tk ":=",
  default ← if default_present.is_some then some <$> texpr
  else pure none,
  handle_member cfgn n val default

meta def custom (cfgn : name) (n : name) : lean.parser unit := do
  tac ← ident,
  of_tactic' $ resolve_name tac >>= iconfig.env_add cfgn n

meta def bool := generic ``(iparam.handler.bool)
meta def nat := generic ``(iparam.handler.nat)
meta def enat := generic ``(iparam.handler.enat)
meta def string := generic ``(iparam.handler.string)
meta def name := generic ``(iparam.handler.name)
meta def lpexpr := generic ``(iparam.handler.lpexpr)
meta def pexpr := generic ``(iparam.handler.pexpr)
meta def list := generic ``(iparam.handler.list)

end iparam

namespace cfgopt.type

open cfgopt.type

meta def to_reader_pexpr : cfgopt.type → _root_.pexpr
| bool := ``(iparam.handler.bool)
| nat  := ``(iparam.handler.nat)
| enat  := ``(iparam.handler.enat)
| string := ``(iparam.handler.string)
| name := ``(iparam.handler.name)
| pexpr := ``(iparam.handler.pexpr)
| (list t) := ``(iparam.handler.list) $ pexpr.of_expr `(t)

end cfgopt.type

namespace iconfig

meta def env_add_struct (cfgn : name) (struct : name) : tactic unit := do
  e ← tactic.get_env,
  l ← iconfig.get_struct_types e struct,
  l.mmap' (λ s, iconfig.env_add cfgn s.1 s.2.to_reader_pexpr)

end iconfig
