import .types

namespace iconfig

meta def default_schema : schema := ⟨none, overload_policy.ignore⟩

namespace schema

-- TODO implement the other policy options
meta def apply (s : schema) : option cfgopt.value → option cfgopt.value
| none := s.default
| (some o) := o

end schema

end iconfig
