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
// Helper to find the smallest period of a string
function Period(s: string): nat
    requires |s| > 0
    ensures 1 <= Period(s) <= |s|
    ensures ApplyShifts(s, Period(s)) == s
    ensures forall k :: 0 < k < Period(s) ==> ApplyShifts(s, k) != s
{
    var periods := set k | 0 < k <= |s| && ApplyShifts(s, k) == s;
    assert |s| in periods by {
        CyclicShiftIdentity(s, 1);
        assert ApplyShifts(s, |s|) == s;
    }
    assert periods != {};
    var minPeriod := MinOfSet(periods);
    assert minPeriod in periods;
    assert ApplyShifts(s, minPeriod) == s;
    assert forall k :: k in periods ==> minPeriod <= k;
    assert forall k :: 0 < k < minPeriod ==> k !in periods by {
        forall k | 0 < k < minPeriod 
            ensures k !in periods
        {
            if k in periods {
                assert minPeriod <= k;
                assert false;
            }
        }
    }
    minPeriod
}

// Helper to prove that shifting by |s| gives back the original string
lemma CyclicShiftIdentity(s: string, n: nat)
    requires |s| > 0
    ensures ApplyShifts(s, n * |s|) == s
    decreases n
{
    if n == 0 {
        assert ApplyShifts(s, 0) == s;
    } else {
        CyclicShiftIdentity(s, n - 1);
        assert ApplyShifts(s, n * |s|) == ApplyShifts(s, |s| + (n-1) * |s|);
        ApplyShiftsComposition(s, (n-1) * |s|, |s|);
        assert ApplyShifts(s, n * |s|) == ApplyShifts(ApplyShifts(s, (n-1) * |s|), |s|);
        assert ApplyShifts(s, (n-1) * |s|) == s;
        CyclicShiftFullRotation(s, 0);
        assert ApplyShifts(s, |s|) == s;
    }
}

// Helper to prove that shifting by |s| steps is identity
lemma CyclicShiftFullRotation(s: string, k: nat)
    requires |s| > 0
    ensures ApplyShifts(s, k + |s|) == ApplyShifts(s, k)
{
    ApplyShiftsComposition(s, k, |s|);
    assert ApplyShifts(s, k + |s|) == ApplyShifts(ApplyShifts(s, k), |s|);
    var s' := ApplyShifts(s, k);
    LengthPreservedByShift(s, k);
    assert |s'| == |s|;
    FullRotationIsIdentity(s');
    assert ApplyShifts(s', |s'|) == s';
    assert ApplyShifts(s, k + |s|) == ApplyShifts(s, k);
}

// Helper lemma to prove that ApplyShifts preserves string length
lemma LengthPreservedByShift(s: string, k: nat)
    requires |s| > 0
    ensures |ApplyShifts(s, k)| == |s|
    decreases k
{
    if k == 0 {
        assert ApplyShifts(s, 0) == s;
    } else {
        LengthPreservedByShift(s, k - 1);
        var s' := ApplyShifts(s, k - 1);
        assert |s'| == |s|;
        assert ApplyShifts(s, k) == CyclicShiftForward(s');
        assert |CyclicShiftForward(s')| == |s'[1..]| + 1 == |s'| - 1 + 1 == |s'| == |s|;
    }
}

// Helper lemma: shifting any string by its length gives back the string
lemma FullRotationIsIdentity(s: string)
    requires |s| > 0
    ensures ApplyShifts(s, |s|) == s
    decreases |s|
{
    if |s| == 1 {
        assert ApplyShifts(s, 1) == CyclicShiftForward(s) == s;
    } else {
        var t := CyclicShiftForward(s);
        assert |t| == |s|;
        ApplyShiftsExpansion(s, |s|);
        assert ApplyShifts(s, |s|) == ApplyShifts(t, |s| - 1);
        
        if |t| == 1 {
            assert ApplyShifts(t, 0) == t;
            assert t == s;
        } else {
            FullRotationIsIdentity(t);
            assert ApplyShifts(t, |t|) == t;
            assert |t| == |s|;
            ApplyShiftsExpansion(t, |t|);
            assert ApplyShifts(t, |t|) == ApplyShifts(CyclicShiftForward(t), |t| - 1);
            assert CyclicShiftForward(t) == CyclicShiftForward(CyclicShiftForward(s));
            assert t == CyclicShiftForward(s);
        }
        
        ApplyShiftsComposition(t, |s| - 1, 1);
        assert ApplyShifts(t, |s|) == ApplyShifts(ApplyShifts(t, |s| - 1), 1);
        assert ApplyShifts(ApplyShifts(t, |s| - 1), 1) == CyclicShiftForward(ApplyShifts(t, |s| - 1));
        assert ApplyShifts(s, |s|) == s;
    }
}

// Helper to expand ApplyShifts
lemma ApplyShiftsExpansion(s: string, n: nat)
    requires |s| > 0
    requires n > 0
    ensures ApplyShifts(s, n) == ApplyShifts(CyclicShiftForward(s), n - 1)
{
    if n == 1 {
        assert ApplyShifts(s, 1) == CyclicShiftForward(ApplyShifts(s, 0)) == CyclicShiftForward(s);
        assert ApplyShifts(CyclicShiftForward(s), 0) == CyclicShiftForward(s);
    } else {
        calc == {
            ApplyShifts(s, n);
            CyclicShiftForward(ApplyShifts(s, n - 1));
            { if n - 1 > 0 { ApplyShiftsExpansion(s, n - 1); } }
            CyclicShiftForward(if n - 1 == 0 then s else ApplyShifts(CyclicShiftForward(s), n - 2));
            ApplyShifts(CyclicShiftForward(s), n - 1);
        }
    }
}

// Composition of shifts
lemma ApplyShiftsComposition(s: string, i: nat, j: nat)
    requires |s| > 0
    ensures ApplyShifts(s, i + j) == ApplyShifts(ApplyShifts(s, i), j)
    decreases j
{
    if j == 0 {
        assert ApplyShifts(s, i + 0) == ApplyShifts(s, i);
        assert ApplyShifts(ApplyShifts(s, i), 0) == ApplyShifts(s, i);
    } else {
        ApplyShiftsComposition(s, i, j - 1);
    }
}

// Helper function to get minimum of a non-empty set
function MinOfSet(s: set<nat>): nat
    requires s != {}
    ensures MinOfSet(s) in s
    ensures forall x :: x in s ==> MinOfSet(s) <= x
{
    var some_element :| some_element in s;
    if s == {some_element} then
        some_element
    else
        var rest := s - {some_element};
        assert rest != {};
        var min_rest := MinOfSet(rest);
        if some_element <= min_rest then some_element else min_rest
}

// Main lemma connecting period to number of distinct shifts
lemma PeriodEqualsDistinctShifts(s: string)
    requires |s| > 0
    ensures |AllDistinctCyclicShifts(s)| == Period(s)
{
    var p := Period(s);
    
    // First show all shifts from 0 to p-1 are distinct
    forall i, j | 0 <= i < p && 0 <= j < p && i != j
        ensures ApplyShifts(s, i) != ApplyShifts(s, j)
    {
        if ApplyShifts(s, i) == ApplyShifts(s, j) {
            if i < j {
                ShiftDifference(s, i, j);
                assert ApplyShifts(s, j - i) == s;
                assert 0 < j - i < p;
                assert false;
            } else {
                ShiftDifference(s, j, i);
                assert ApplyShifts(s, i - j) == s;
                assert 0 < i - j < p;
                assert false;
            }
        }
    }
    
    // Then show any shift k >= p equals some shift from 0 to p-1
    forall k | 0 <= k < |s|
        ensures exists j :: 0 <= j < p && ApplyShifts(s, k) == ApplyShifts(s, j)
    {
        var j := k % p;
        assert 0 <= j < p;
        ShiftModuloPeriod(s, k, p);
        assert ApplyShifts(s, k) == ApplyShifts(s, j);
    }
    
    // Show the set of distinct shifts equals shifts from 0 to p-1
    var distinctShifts := set i | 0 <= i < p :: ApplyShifts(s, i);
    
    // Prove that this set has exactly p elements
    var indices := set i | 0 <= i < p;
    assert |indices| == p;
    
    // The mapping from indices to shifts is injective
    forall i1, i2 | i1 in indices && i2 in indices && ApplyShifts(s, i1) == ApplyShifts(s, i2)
        ensures i1 == i2
    {
        if i1 != i2 {
            assert ApplyShifts(s, i1) != ApplyShifts(s, i2);
            assert false;
        }
    }
    
    assert |distinctShifts| == |indices| == p;
    
    forall x | x in AllDistinctCyclicShifts(s)
        ensures x in distinctShifts
    {
        assert exists i :: 0 <= i < |s| && x == ApplyShifts(s, i);
        var i :| 0 <= i < |s| && x == ApplyShifts(s, i);
        var j := i % p;
        assert ApplyShifts(s, i) == ApplyShifts(s, j);
        assert x in distinctShifts;
    }
    
    forall x | x in distinctShifts
        ensures x in AllDistinctCyclicShifts(s)
    {
        assert exists i :: 0 <= i < p && x == ApplyShifts(s, i);
        var i :| 0 <= i < p && x == ApplyShifts(s, i);
        assert i < |s|;
        assert x in AllDistinctCyclicShifts(s);
    }
    
    assert AllDistinctCyclicShifts(s) == distinctShifts;
    assert |AllDistinctCyclicShifts(s)| == p;
}

// Helper lemma for shift invariance
lemma ShiftInvariance(s: string, i: nat, d: nat)
    requires |s| > 0
    requires ApplyShifts(s, i) == ApplyShifts(ApplyShifts(s, i), d)
    ensures ApplyShifts(s, d) == s
{
    ApplyShiftsComposition(s, i, d);
    assert ApplyShifts(s, i + d) == ApplyShifts(s, i);
    ShiftDifference(s, i, i + d);
}

// Helper for shift difference
lemma ShiftDifference(s: string, i: nat, j: nat)
    requires |s| > 0
    requires i <= j
    requires ApplyShifts(s, i) == ApplyShifts(s, j)
    ensures ApplyShifts(s, j - i) == s
{
    if i == j {
        assert j - i == 0;
        assert ApplyShifts(s, 0) == s;
    } else {
        ApplyShiftsComposition(s, i, j - i);
        assert ApplyShifts(s, j) == ApplyShifts(ApplyShifts(s, i), j - i);
        assert ApplyShifts(s, i) == ApplyShifts(ApplyShifts(s, i), j - i);
        
        var s' := ApplyShifts(s, i);
        assert s' == ApplyShifts(s', j - i);
        LengthPreservedByShift(s, i);
        assert |s'| == |s|;
        
        // s' is invariant under shift by j-i, so j-i must be a multiple of period of s'
        var p' := Period(s');
        assert ApplyShifts(s', p') == s';
        assert (j - i) % p' == 0 || ApplyShifts(s', (j - i) % p') == s';
        
        // But we need to show ApplyShifts(s, j - i) == s
        // Use the fact that shifting s' back gives s eventually
        ShiftInverseExists(s, i, s');
    }
}

lemma ShiftInverseExists(s: string, k: nat, s': string)
    requires |s| > 0
    requires s' == ApplyShifts(s, k)
    requires |s'| == |s|
    requires ApplyShifts(s', |s| - (k % |s|)) == s || k == 0
{
    if k == 0 {
        assert s' == s;
    } else {
        LengthPreservedByShift(s, k);
        var inv := |s| - (k % |s|);
        if k % |s| == 0 {
            assert inv == |s|;
            FullRotationIsIdentity(s');
        } else {
            ApplyShiftsComposition(s, k, inv);
            assert ApplyShifts(s, k + inv) == ApplyShifts(s', inv);
            assert k + inv == k + |s| - (k % |s|);
            var total := k + |s| - (k % |s|);
            assert total % |s| == 0;
            ShiftByMultipleOfLength(s, total / |s|);
        }
    }
}

// If shifting a string by k gives the same string, then k is a multiple of the period
lemma UniqueInverse(s: string, k: nat)
    requires |s| > 0
    requires ApplyShifts(s, k) == s
    ensures k == 0 || k % |s| == 0 || ApplyShifts(s, k % |s|) == s
{
    if k > 0 && k % |s| != 0 {
        var q := k / |s|;
        var r := k % |s|;
        assert k == q * |s| + r;
        assert 0 < r < |s|;
        ShiftByMultipleOfLength(s, q);
        ApplyShiftsComposition(s, q * |s|, r);
        assert ApplyShifts(s, k) == ApplyShifts(s, r);
    }
}

// Shifting by multiples of period
lemma ShiftModuloPeriod(s: string, k: nat, p: nat)
    requires |s| > 0
    requires p == Period(s)
    ensures ApplyShifts(s, k) == ApplyShifts(s, k % p)
{
    var q := k / p;
    var r := k % p;
    assert k == q * p + r;
    
    ShiftByMultipleOfPeriod(s, q, p);
    ApplyShiftsComposition(s, q * p, r);
}

// Helper for shifting by multiples of period
lemma ShiftByMultipleOfPeriod(s: string, q: nat, p: nat)
    requires |s| > 0
    requires p == Period(s)
    ensures ApplyShifts(s, q * p) == s
    decreases q
{
    if q == 0 {
        assert ApplyShifts(s, 0) == s;
    } else {
        ShiftByMultipleOfPeriod(s, q - 1, p);
        ApplyShiftsComposition(s, (q - 1) * p, p);
        assert ApplyShifts(s, q * p) == ApplyShifts(ApplyShifts(s, (q - 1) * p), p);
        assert ApplyShifts(s, (q - 1) * p) == s;
        assert ApplyShifts(s, p) == s;
    }
}

// Helper for shifting by multiples of string length
lemma ShiftByMultipleOfLength(s: string, q: nat)
    requires |s| > 0
    ensures ApplyShifts(s, q * |s|) == s
{
    CyclicShiftIdentity(s, q);
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
    PeriodEqualsDistinctShifts(s);
    result := Period(s);
}
// </vc-code>

