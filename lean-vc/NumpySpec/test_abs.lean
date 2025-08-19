import DafnySpecs.NpAbs

open DafnySpecs.NpAbs

-- Test the abs function
#eval abs #[1, -2, 3, -4, 5]
-- Expected: #[1, 2, 3, 4, 5]

#eval abs #[-10, 0, 10]
-- Expected: #[10, 0, 10]

-- Test with empty array
#eval abs #[]
-- Expected: #[]

-- Test idempotency
#eval abs (abs #[1, -2, 3])
-- Expected: #[1, 2, 3]