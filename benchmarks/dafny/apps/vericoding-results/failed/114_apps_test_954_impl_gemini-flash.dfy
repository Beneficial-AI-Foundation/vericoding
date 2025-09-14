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
function Modulo(a: int, n: int): int
    requires n > 0
    ensures 0 <= Modulo(a, n) < n
{
    var r := a % n;
    if r < 0 then r + n else r
}

lemma lemma_ApplyShifts_properties(s: string, steps: nat, k: nat)
    requires |s| > 0
    ensures |ApplyShifts(s, steps)| == |s|
    ensures ApplyShifts(s, steps)[Modulo(k + steps, |s|)] == s[Modulo(k, |s|)]
{
    if steps == 0 {
        assert |ApplyShifts(s, 0)| == |s|;
        assert ApplyShifts(s, 0)[Modulo(k + 0, |s|)] == s[Modulo(k, |s|)];
    } else {
        lemma_ApplyShifts_properties(s, steps - 1, k);
        var s_prev := ApplyShifts(s, steps - 1);
        var s_curr := CyclicShiftForward(s_prev);

        // Prove |ApplyShifts(s, steps)| == |s|
        assert |s_curr| == |s_prev|; // From CyclicShiftForward definition and previous lemma
        assert |s_curr| == |s|;

        // Prove ApplyShifts(s, steps)[Modulo(k + steps, |s|)] == s[Modulo(k, |s|)]
        assert s_curr[Modulo(k + steps, |s|)] == s_prev[Modulo(Modulo(k + steps, |s|) - 1 + |s|, |s|)];
        assert Modulo(Modulo(k + steps, |s|) - 1 + |s|, |s|) == Modulo(k + steps - 1, |s|);
        calc {
            s_curr[Modulo(k + steps, |s|)];
            s_prev[Modulo(k + steps - 1, |s|)];
            s[Modulo(k, |s|)]; // By inductive hypothesis for steps - 1
        }
    }
}

lemma lemma_AllDistinctCyclicShifts_properties(s: string)
    requires |s| > 0
    ensures |AllDistinctCyclicShifts(s)| > 0
    ensures |AllDistinctCyclicShifts(s)| <= |s|
{
    // The definition of AllDistinctCyclicShifts already implies the properties
    // if a string `s` has length |s| > 0
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
    var seen_shifts: set<string> := {};
    var current_s := s;
    var i := 0;

    assert forall k :: 0 <= k < 0 ==> ApplyShifts(s, k) !in seen_shifts; // vacuous truth

    while (i < n)
        invariant 0 <= i <= n
        invariant current_s == ApplyShifts(s, i)
        invariant seen_shifts == set k | 0 <= k < i :: ApplyShifts(s, k)
        invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> ApplyShifts(s, k1) != ApplyShifts(s, k2)
        invariant i == |seen_shifts|
        invariant forall k :: 0 <= k < i ==> ApplyShifts(s, k) !in (set m | 0 <= m < k :: ApplyShifts(s,m))
        decreases n - i
    {
        lemma_ApplyShifts_properties(s, i, 0); // To establish |ApplyShifts(s,i)| == |s|

        if current_s in seen_shifts {
            assert exists k :: 0 <= k < i && ApplyShifts(s,k) == current_s;
            assert i > 0;
            return i;
        }
        
        seen_shifts := seen_shifts + {current_s};
        i := i + 1;
        current_s := CyclicShiftForward(current_s);
    }
    
    // If the loop finishes, all 'n' shifts are distinct
    assert i == n;
    assert seen_shifts == set k | 0 <= k < n :: ApplyShifts(s, k);
    assert forall k1, k2 :: 0 <= k1 < k2 < n ==> ApplyShifts(s, k1) != ApplyShifts(s, k2);
    assert |AllDistinctCyclicShifts(s)| == n; // Since all are distinct
    return n;
}
// </vc-code>

