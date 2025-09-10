function CyclicShiftForward(s: string): string
    requires |s| > 0
{
    s[1..] + [s[0]]
}

predicate ValidInput(s: string)
{
    |s| > 0
}

function ApplyShifts(s: string, steps: nat): string
    requires |s| > 0
    decreases steps
{
    if steps == 0 then s
    else CyclicShiftForward(ApplyShifts(s, steps - 1))
}

function AllDistinctCyclicShifts(s: string): set<string>
    requires |s| > 0
{
    set i | 0 <= i < |s| :: ApplyShifts(s, i)
}

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  ghost var seen: set<string> := set j | 0 <= j < 0 :: ApplyShifts(s, j);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant seen == set j | 0 <= j < i :: ApplyShifts(s, j)
  {
    seen := set j | 0 <= j < i+1 :: ApplyShifts(s, j);
    i := i + 1;
  }
  assert i == n;
  assert seen == AllDistinctCyclicShifts(s);
  result := |seen|;
  assert result == |AllDistinctCyclicShifts(s)|;
  assert ApplyShifts(s, 0) in seen;
  assert 1 <= result;
  assert result <= n;
}
// </vc-code>

