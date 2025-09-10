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

    while (i < n)
        invariant 0 <= i <= n
        invariant current_s == ApplyShifts(s, i)
        invariant seen_shifts == set k | 0 <= k < i :: ApplyShifts(s, k)
        invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> ApplyShifts(s, k1) != ApplyShifts(s, k2)
        decreases n - i
    {
        lemma_ApplyShifts_properties(s, i, 0); // To establish |ApplyShifts(s,i)| == |s|
        if current_s in seen_shifts {
            return i;
        }
        seen_shifts := seen_shifts + {current_s};
        i := i + 1;
        current_s := CyclicShiftForward(current_s);
    }
    return n;
}
// </vc-code>

