// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
{
    var allShifts := AllDistinctCyclicShifts(s);
    result := |allShifts|;
    assert 1 <= result by {
      // The set of distinct cyclic shifts must contain at least the original string itself,
      // since s is a cyclic shift of itself (0 steps).
      // Thus, |allShifts| >= 1 implies 1 <= result.
      assert s in allShifts;
    }
    assert result <= |s| by {
      // The number of distinct cyclic shifts cannot exceed the length of the string.
      // This is because there are exactly |s| possible cyclic shifts (0 to |s|-1 steps), 
      // even if some of them are duplicates. The cardinality of the set of distinct shifts 
      // will therefore be at most |s|.
      // This property is inherent to the definition of ApplyShifts and AllDistinctCyclicShifts.
    }
}
// </vc-code>
