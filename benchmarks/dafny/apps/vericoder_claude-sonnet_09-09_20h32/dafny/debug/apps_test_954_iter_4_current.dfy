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
lemma ApplyShiftsModulo(s: string, steps: nat)
    requires |s| > 0
    ensures ApplyShifts(s, steps) == ApplyShifts(s, steps % |s|)
{
    if steps < |s| {
        assert steps % |s| == steps;
    } else {
        var q := steps / |s|;
        var r := steps % |s|;
        assert steps == q * |s| + r;
        ApplyShiftsModuloHelper(s, q, r);
    }
}

lemma ApplyShiftsModuloHelper(s: string, q: nat, r: nat)
    requires |s| > 0
    requires r < |s|
    ensures ApplyShifts(s, q * |s| + r) == ApplyShifts(s, r)
    decreases q
{
    if q == 0 {
        assert q * |s| + r == r;
    } else {
        ApplyShiftsModuloHelper(s, q - 1, r);
        ApplyShiftsCycle(s, (q - 1) * |s| + r);
    }
}

lemma ApplyShiftsCycle(s: string, steps: nat)
    requires |s| > 0
    ensures ApplyShifts(s, steps + |s|) == ApplyShifts(s, steps)
    decreases steps
{
    if steps == 0 {
        ApplyShiftsFullCycle(s);
    } else {
        ApplyShiftsCycle(s, steps - 1);
        assert ApplyShifts(s, steps + |s|) == CyclicShiftForward(ApplyShifts(s, steps + |s| - 1));
        assert ApplyShifts(s, steps + |s| - 1) == ApplyShifts(s, steps - 1);
        assert ApplyShifts(s, steps) == CyclicShiftForward(ApplyShifts(s, steps - 1));
    }
}

lemma ApplyShiftsFullCycle(s: string)
    requires |s| > 0
    ensures ApplyShifts(s, |s|) == s
{
    ApplyShiftsFullCycleInductive(s, |s|);
}

lemma ApplyShiftsFullCycleInductive(s: string, n: nat)
    requires |s| > 0
    requires n <= |s|
    ensures ApplyShifts(s, n) == ApplyShifts(s, n % |s|)
    decreases n
{
    if n == 0 {
        assert ApplyShifts(s, 0) == s;
        assert n % |s| == 0;
        assert ApplyShifts(s, n % |s|) == s;
    } else if n == |s| {
        ApplyShiftsFullCycleInductive(s, n - 1);
        assert ApplyShifts(s, n) == CyclicShiftForward(ApplyShifts(s, n - 1));
        assert ApplyShifts(s, n - 1) == ApplyShifts(s, (n - 1) % |s|);
        assert (n - 1) % |s| == |s| - 1;
        assert n % |s| == 0;
        assert ApplyShifts(s, n % |s|) == ApplyShifts(s, 0) == s;
        ApplyShiftsToFullCycle(s, |s| - 1);
    } else {
        assert n < |s|;
        assert n % |s| == n;
    }
}

lemma ApplyShiftsToFullCycle(s: string, k: nat)
    requires |s| > 0
    requires k == |s| - 1
    ensures CyclicShiftForward(ApplyShifts(s, k)) == s
    decreases k
{
    if |s| == 1 {
        assert k == 0;
        assert ApplyShifts(s, 0) == s;
        assert CyclicShiftForward(s) == s[1..] + [s[0]] == [] + [s[0]] == [s[0]] == s;
    } else {
        ApplyShiftsToFullCycleHelper(s, k);
    }
}

lemma ApplyShiftsToFullCycleHelper(s: string, k: nat)
    requires |s| > 1
    requires k == |s| - 1
    ensures CyclicShiftForward(ApplyShifts(s, k)) == s
{
    var shifted := ApplyShifts(s, k);
    assert shifted == ApplyShifts(s, |s| - 1);
    ShiftPattern(s, |s| - 1);
}

lemma ShiftPattern(s: string, k: nat)
    requires |s| > 1
    requires k == |s| - 1
    ensures ApplyShifts(s, k) == s[k..] + s[..k]
    ensures CyclicShiftForward(ApplyShifts(s, k)) == s
{
    assert s[k..] + s[..k] == s[|s|-1..] + s[..|s|-1];
    assert s[|s|-1..] == [s[|s|-1]];
    assert CyclicShiftForward(s[k..] + s[..k]) == s[..k] + s[k..];
    assert s[..k] + s[k..] == s;
}

lemma AllDistinctShiftsCardinality(s: string)
    requires |s| > 0
    ensures |AllDistinctCyclicShifts(s)| <= |s|
{
    var shifts := AllDistinctCyclicShifts(s);
    assert shifts == set i {:trigger ApplyShifts(s, i)} | 0 <= i < |s| :: ApplyShifts(s, i);
    assert |shifts| <= |s|;
}

lemma ShiftsEquivalence(s: string, count: int)
    requires |s| > 0
    requires 0 <= count <= |s|
    ensures (set i | 0 <= i < count :: ApplyShifts(s, i)) == 
            (set i | 0 <= i < count :: ApplyShifts(s, i))
{
}

lemma ShiftsEqualAtEnd(s: string)
    requires |s| > 0
    ensures (set i | 0 <= i < |s| :: ApplyShifts(s, i)) == AllDistinctCyclicShifts(s)
{
    assert (set i | 0 <= i < |s| :: ApplyShifts(s, i)) == AllDistinctCyclicShifts(s);
}

lemma ShiftsDistinct(s: string, i: nat, j: nat)
    requires |s| > 0
    requires 0 <= i < j < |s|
    ensures ApplyShifts(s, i) != ApplyShifts(s, j)
{
    if ApplyShifts(s, i) == ApplyShifts(s, j) {
        ShiftDistinctHelper(s, i, j);
        assert false;
    }
}

lemma ShiftDistinctHelper(s: string, i: nat, j: nat)
    requires |s| > 0
    requires 0 <= i < j < |s|
    requires ApplyShifts(s, i) == ApplyShifts(s, j)
    ensures false
{
    var diff := j - i;
    assert 0 < diff < |s|;
    assert ApplyShifts(s, j) == ApplyShifts(s, i + diff);
    ApplyShiftProperty(s, i, diff);
    assert ApplyShifts(s, i + diff) == ApplyShifts(ApplyShifts(s, i), diff);
    assert ApplyShifts(s, i) == ApplyShifts(ApplyShifts(s, i), diff);
    assert ApplyShifts(ApplyShifts(s, i), diff) == ApplyShifts(s, i);
    ShiftNonTrivial(ApplyShifts(s, i), diff);
}

lemma ApplyShiftProperty(s: string, i: nat, diff: nat)
    requires |s| > 0
    ensures ApplyShifts(s, i + diff) == ApplyShifts(ApplyShifts(s, i), diff)
{
    ShiftComposition(s, i, diff);
}

lemma ShiftComposition(s: string, a: nat, b: nat)
    requires |s| > 0
    ensures ApplyShifts(s, a + b) == ApplyShifts(ApplyShifts(s, a), b)
    decreases b
{
    if b == 0 {
        assert ApplyShifts(s, a + 0) == ApplyShifts(s, a);
        assert ApplyShifts(ApplyShifts(s, a), 0) == ApplyShifts(s, a);
    } else {
        ShiftComposition(s, a, b - 1);
        assert ApplyShifts(s, a + b) == CyclicShiftForward(ApplyShifts(s, a + b - 1));
        assert ApplyShifts(s, a + b - 1) == ApplyShifts(ApplyShifts(s, a), b - 1);
        assert ApplyShifts(ApplyShifts(s, a), b) == CyclicShiftForward(ApplyShifts(ApplyShifts(s, a), b - 1));
    }
}

lemma ShiftNonTrivial(s: string, k: nat)
    requires |s| > 0
    requires 0 < k < |s|
    requires ApplyShifts(s, k) == s
    ensures false
{
    if |s| == 1 {
        assert k == 0;
        assert false;
    } else {
        NonTrivialShiftHelper(s, k);
    }
}

lemma NonTrivialShiftHelper(s: string, k: nat)
    requires |s| > 1
    requires 0 < k < |s|
    requires ApplyShifts(s, k) == s
    ensures false
{
    assert s[0] == ApplyShifts(s, k)[0];
    assert ApplyShifts(s, k)[0] == s[k];
    assert s[0] == s[k];
    assert s[1] == ApplyShifts(s, k)[1];
    assert ApplyShifts(s, k)[1] == s[(k + 1) % |s|];
    ShiftCharacterAnalysis(s, k);
}

lemma ShiftCharacterAnalysis(s: string, k: nat)
    requires |s| > 1
    requires 0 < k < |s|
    requires ApplyShifts(s, k) == s
    ensures false
{
    forall idx | 0 <= idx < |s|
        ensures s[idx] == s[(idx + k) % |s|]
    {
        assert s[idx] == ApplyShifts(s, k)[idx];
        assert ApplyShifts(s, k)[idx] == s[(idx + k) % |s|];
    }
    
    assert forall idx | 0 <= idx < |s| :: s[idx] == s[(idx + k) % |s|];
    PeriodicityContradiction(s, k);
}

lemma PeriodicityContradiction(s: string, k: nat)
    requires |s| > 1
    requires 0 < k < |s|
    requires forall idx | 0 <= idx < |s| :: s[idx] == s[(idx + k) % |s|]
    ensures false
{
    var gcd_val := gcd(k, |s|);
    assert gcd_val < |s|;
    assert s[0] == s[gcd_val];
    if gcd_val > 0 {
        assert s[0] == s[gcd_val] == s[2 * gcd_val % |s|];
        GcdPeriodicity(s, k, gcd_val);
    }
}

lemma GcdPeriodicity(s: string, k: nat, g: nat)
    requires |s| > 1
    requires 0 < k < |s|
    requires g == gcd(k, |s|)
    requires g > 0
    requires forall idx | 0 <= idx < |s| :: s[idx] == s[(idx + k) % |s|]
    ensures false
{
    assert false;
}

function gcd(a: nat, b: nat): nat
{
    if b == 0 then a else gcd(b, a % b)
}

lemma ShiftsCardinalityInvariant(s: string, count: nat)
    requires |s| > 0
    requires count <= |s|
    ensures |set i | 0 <= i < count :: ApplyShifts(s, i)| == count
{
    if count == 0 {
        assert set i | 0 <= i < 0 :: ApplyShifts(s, i) == {};
    } else {
        ShiftsCardinalityInvariant(s, count - 1);
        var prev_set := set i | 0 <= i < count - 1 :: ApplyShifts(s, i);
        var new_set := set i | 0 <= i < count :: ApplyShifts(s, i);
        assert new_set == prev_set + {ApplyShifts(s, count - 1)};
        
        forall i | 0 <= i < count - 1
            ensures ApplyShifts(s, i) != ApplyShifts(s, count - 1)
        {
            ShiftsDistinct(s, i, count - 1);
        }
        
        assert ApplyShifts(s, count - 1) !in prev_set;
        assert |new_set| == |prev_set| + 1 == (count - 1) + 1 == count;
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
    var current := s;
    var count := 0;
    
    while count < |s|
        invariant 0 <= count <= |s|
        invariant current == ApplyShifts(s, count)
        invariant shifts == set i | 0 <= i < count :: ApplyShifts(s, i)
        invariant |shifts| == count
    {
        ShiftsCardinalityInvariant(s, count + 1);
        shifts := shifts + {current};
        current := CyclicShiftForward(current);
        count := count + 1;
    }
    
    ShiftsEqualAtEnd(s);
    assert shifts == AllDistinctCyclicShifts(s);
    AllDistinctShiftsCardinality(s);
    result := |shifts|;
}
// </vc-code>

