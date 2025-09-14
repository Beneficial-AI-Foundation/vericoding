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
lemma {:induction steps} ApplyShifts_preserves_length(s: string, steps: nat)
    requires |s| > 0
    ensures |ApplyShifts(s, steps)| == |s|
    decreases steps
{
    if steps > 0 {
        ApplyShifts_preserves_length(s, steps - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
{
    var shifts: set<string> := {};
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant shifts == (set k | 0 <= k < i :: ApplyShifts(s, k))
    {
        shifts := shifts + {ApplyShifts(s, i)};
        i := i + 1;
    }
    result := |shifts|;
}
// </vc-code>

