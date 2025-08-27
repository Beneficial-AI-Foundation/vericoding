/-!
Shim module to satisfy case-sensitive imports on Linux.

Many specs import `Benchmarks.Clever.CommonDefs`, while the original file
resides under `Benchmarks/clever/CommonDefs.lean`. This wrapper imports the
lowercase path so both module names work.
-/

import Benchmarks.clever.CommonDefs

-- Re-export common definitions (optional; simple import is sufficient)
-- open the namespace as needed here, if there was one.

