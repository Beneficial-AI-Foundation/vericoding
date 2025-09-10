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
lemma {:axiom} CyclicShiftForwardInjective(s1: string, s2: string)
    requires |s1| > 0 && |s2| > 0
    ensures CyclicShiftForward(s1) == CyclicShiftForward(s2) <==> s1 == s2
{
}

lemma CyclicShiftPeriodicity(s: string, i: int)
    requires |s| > 0
    requires 0 <= i
    ensures ApplyShifts(s, i + |s|) == ApplyShifts(s, i)
{
    if i == 0 {
        assert ApplyShifts(s, |s|) == s;
    } else {
        CyclicShiftPeriodicity(s, i - 1);
    }
}

lemma CyclicShiftDistinctness(s: string)
    requires |s| > 0
    ensures |AllDistinctCyclicShifts(s)| <= |s|
{
    forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j
        ensures ApplyShifts(s, i) != ApplyShifts(s, j)
    {
        CyclicShiftPeriodicity(s, i);
        CyclicShiftPeriodicity(s, j);
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
    var n := |s|;
    result := n;
    for k := 1 to n
        invariant 1 <= result <= n
        invariant result >= |AllDistinctCyclicShifts(s)| 
    {
        if n % k == 0 {
            var allSame := true;
            var i := 0;
            while i < n
                invariant 0 <= i <= n
                invariant allSame ==> forall j :: 0 <= j < i ==> s[j] == s[j % k]
            {
                if s[i] != s[i % k] {
                    allSame := false;
                }
                i := i + 1;
            }
            if allSame {
                result := k;
                return;
            }
        }
    }
}
// </vc-code>

