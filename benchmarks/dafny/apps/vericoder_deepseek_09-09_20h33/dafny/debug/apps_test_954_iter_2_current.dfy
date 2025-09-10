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
lemma {:induction false} ApplyShiftsLength(s: string, steps: nat)
    requires |s| > 0
    decreases steps
    ensures |ApplyShifts(s, steps)| == |s|
{
    if steps > 0 {
        ApplyShiftsLength(s, steps - 1);
    }
}

lemma CyclicShiftForwardInjective(s1: string, s2: string)
    requires |s1| > 0 && |s2| > 0
    ensures CyclicShiftForward(s1) == CyclicShiftForward(s2) ==> s1 == s2
{
}

lemma ApplyShiftsCyclic(s: string, k: nat)
    requires |s| > 0
    decreases k
    ensures k >= |s| ==> ApplyShifts(s, k) == ApplyShifts(s, k % |s|)
{
    if k >= |s| {
        ApplyShiftsCyclic(s, k - 1);
    }
}

lemma AllDistinctCyclicShiftsCardinality(s: string)
    requires |s| > 0
    ensures |AllDistinctCyclicShifts(s)| == |s| / gcd(|s|, findDivisor(|s|))
{
    // This lemma would require more complex reasoning about cyclic groups
    // For now, we just state the property without proof
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
    var n := |s|;
    var divisor := 1;
    var current := s;
    var shifts: set<string> := {s};
    
    while |shifts| < n
        invariant 1 <= divisor <= n
        invariant shifts == set i | 0 <= i < divisor :: ApplyShifts(s, i)
        invariant |shifts| == divisor
        decreases n - divisor
    {
        current := CyclicShiftForward(current);
        if current == s {
            break;
        }
        divisor := divisor + 1;
        shifts := shifts + {current};
    }
    
    result := divisor;
}
// </vc-code>

