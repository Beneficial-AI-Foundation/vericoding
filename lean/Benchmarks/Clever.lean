/-!
# Clever Benchmarks

Entry point that aggregates Clever benchmark specifications. We prefer
self-contained problem modules without a shared `CommonDefs` to reduce
coupling and avoid accidental circular imports.
-/

import Benchmarks.Clever.Problems.Problem0

-- Add further problems here as they are ported/refined.
