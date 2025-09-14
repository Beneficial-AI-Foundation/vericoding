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
    assert forall k :: 0 < k < minPeriod ==> ApplyShifts(s, k) != s;
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
{
    if |s| == 1 {
        assert ApplyShifts(s, 1) == CyclicShiftForward(s) == s;
    } else {
        FullRotationIsIdentityHelper(s, |s|);
    }
}

lemma FullRotationIsIdentityHelper(s: string, n: nat)
    requires |s| > 0
    requires n == |s|
    ensures ApplyShifts(s, n) == s
    decreases n
{
    if n == 0 {
        assert ApplyShifts(s, 0) == s;
    } else if n == 1 {
        assert |s| == 1;
        assert ApplyShifts(s, 1) == CyclicShiftForward(s) == s;
    } else {
        ApplyShiftsComposition(s, 1, n - 1);
        var t := CyclicShiftForward(s);
        assert |t| == |s|;
        assert ApplyShifts(s, n) == ApplyShifts(t, n - 1);
        
        if n - 1 == |t| {
            FullRotationIsIdentityHelper(t, n - 1);
            assert ApplyShifts(t, n - 1) == t;
            assert t == CyclicShiftForward(s);
            assert s == s[..1] + s[1..];
            assert t == s[1..] + s[..1];
            assert ApplyShifts(t, n - 1) == t;
            
            // We need to show that shifting t by n-1 and then once more gives s
            ApplyShiftsComposition(s, n - 1, 1);
            assert ApplyShifts(s, n) == ApplyShifts(ApplyShifts(s, n - 1), 1);
            
            // Show that n shifts of s gives back s
            CyclicShiftIdentity(s, 1);
        }
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
    decreases s
{
    var some_element :| some_element in s;
    if forall x :: x in s ==> some_element <= x then
        some_element
    else
        var y :| y in s && y < some_element;
        MinOfSet(s - {some_element})
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
    var indices := set i : nat | 0 <= i < p;
    CardinalityOfRange(p);
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

lemma CardinalityOfRange(n: nat)
    ensures |set i : nat | 0 <= i < n| == n
{
    if n == 0 {
        assert |set i : nat | 0 <= i < 0| == 0;
    } else {
        CardinalityOfRange(n - 1);
        var s := set i : nat | 0 <= i < n;
        var s' := set i : nat | 0 <= i < n - 1;
        assert s == s' + {n - 1};
        assert |s| == |s'| + 1 == n - 1 + 1 == n;
    }
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
        
        // Since s' == ApplyShifts(s', j - i), we have that j - i is a multiple of Period(s')
        var p' := Period(s');
        assert ApplyShifts(s', p') == s';
        
        // But we also need to relate back to s
        // Key insight: if ApplyShifts(s, i) has the same period structure
        ShiftInverseRelation(s, i, j - i);
    }
}

lemma ShiftInverseRelation(s: string, i: nat, d: nat)
    requires |s| > 0
    requires ApplyShifts(s, i) == ApplyShifts(ApplyShifts(s, i), d)
    ensures ApplyShifts(s, d) == s
{
    var s' := ApplyShifts(s, i);
    assert s' == ApplyShifts(s', d);
    LengthPreservedByShift(s, i);
    assert |s'| == |s|;
    
    ApplyShiftsComposition(s, i, d);
    assert ApplyShifts(s, i + d) == ApplyShifts(s', d) == s';
    assert ApplyShifts(s, i + d) == ApplyShifts(s, i);
    
    // Now we know ApplyShifts(s, i) == ApplyShifts(s, i + d)
    // This means d is a multiple of the period of the shifted sequence
    
    if d == 0 {
        assert ApplyShifts(s, 0) == s;
    } else if d % |s| == 0 {
        var k := d / |s|;
        CyclicShiftIdentity(s, k);
        assert ApplyShifts(s, d) == s;
    } else {
        // Use the fact that the composition gives us the original
        ApplyShiftsComposition(s, d, i);
        assert ApplyShifts(s, d + i) == ApplyShifts(ApplyShifts(s, d), i);
        assert ApplyShifts(s, i + d) == ApplyShifts(s, i);
        
        // Special handling for the general case
        GeneralShiftInverse(s, i, d);
    }
}

lemma GeneralShiftInverse(s: string, i: nat, d: nat)
    requires |s| > 0
    requires ApplyShifts(s, i) == ApplyShifts(s, i + d)
    ensures ApplyShifts(s, d) == s
{
    if d % |s| == 0 {
        var k := d / |s|;
        CyclicShiftIdentity(s, k);
    } else {
        // The key insight: if shifting by i gives the same result as shifting by i+d,
        // then d must be a period of s
        var p := Period(s);
        assert ApplyShifts(s, p) == s;
        
        // Since ApplyShifts(s, i) == ApplyShifts(s, i + d), we have a periodicity
        if d < p {
            // If d < p and ApplyShifts(s, d) != s, this contradicts minimality of p
            // But we know from the equality that there's a period relationship
            assert ApplyShifts(s, d) == s;
        } else {
            // d >= p, so we can reduce modulo p
            var r := d % p;
            ShiftModuloPeriod(s, d, p);
            assert ApplyShifts(s, d) == ApplyShifts(s, r);
            if r == 0 {
                assert ApplyShifts(s, 0) == s;
                assert ApplyShifts(s, d) == s;
            } else {
                // This case needs the period property
                assert ApplyShifts(s, r) == s;
                assert ApplyShifts(s, d) == s;
            }
        }
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

