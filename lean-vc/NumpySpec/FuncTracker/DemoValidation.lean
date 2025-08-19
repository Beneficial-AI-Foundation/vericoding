import FuncTracker.BasicV2
import FuncTracker.SimpleValidation

namespace FuncTracker.DemoValidation

open FuncTracker

-- This works: all identifiers exist
def validTable := funcTable! "╔═══════════════════════════════════════╗
│ Name                 │ Status │ File   │
╠═══════════════════════════════════════╣
│ List.map             │ ✓✓✓    │ -      │
│ Array.map            │ ✓✓✓    │ -      │
│ Option.map           │ ✓✓✓    │ -      │
╚═══════════════════════════════════════╝"

#eval validTable.functions.size

-- If you uncomment this, it will fail at compile time
-- because ThisDoesNotExist is not a valid identifier:
/-
def invalidTable := funcTable! "╔═══════════════════════════════════════╗
│ Name                 │ Status │ File   │
╠═══════════════════════════════════════╣
│ List.map             │ ✓✓✓    │ -      │
│ ThisDoesNotExist     │ ✓      │ -      │
╚═══════════════════════════════════════╝"
-/

end FuncTracker.DemoValidation