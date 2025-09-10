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
lemma shift_add(s: string, a: nat, b: nat)
    requires |s| > 0
    ensures ApplyShifts(s, a + b) == ApplyShifts(ApplyShifts(s, a), b)
    decreases b
{
    if b == 0 {
        // trivial
    } else {
        shift_add(s, a, b - 1);
        // ApplyShifts(s, a + b) == CyclicShiftForward(ApplyShifts(s, a + b - 1))
        // == CyclicShiftForward(ApplyShifts(ApplyShifts(s, a), b - 1))
        // == ApplyShifts(ApplyShifts(s, a), b)
    }
}

lemma shift_commute(s: string, a: nat, b: nat)
    requires |s| > 0
    ensures ApplyShifts(ApplyShifts(s, a), b) == ApplyShifts(ApplyShifts(s, b), a)
{
    // ApplyShifts(ApplyShifts(s,a),b) == ApplyShifts(s, a+b) == ApplyShifts(ApplyShifts(s,b), a)
    shift_add(s, a, b);
    shift_add(s, b, a);
}

lemma shift_index(s: string, i: nat, p: int)
    requires |s| > 0
    requires 0 <= p < |s|
    ensures ApplyShifts(s, i)[p] == s[(p + i) % |s|]
    decreases i
{
    if i == 0 {
        // ApplyShifts(s,0) == s
    } else {
        // ApplyShifts(s,i) == CyclicShiftForward(ApplyShifts(s,i-1))
        // handle indexing
        if p < |s| - 1 {
            // ApplyShifts(s,i)[p] == ApplyShifts(s,i-1)[p+1]
            shift_index(s, i - 1, p + 1);
        } else {
            // p == |s|-1
            // ApplyShifts(s,i)[|s|-1] == ApplyShifts(s,i-1)[0]
            shift_index(s, i - 1, 0);
        }
    }
}

lemma shift_n_is_identity(s: string)
    requires |s| > 0
    ensures ApplyShifts(s, |s|) == s
{
    var n := |s|;
    // Show for all positions p, ApplyShifts(s,n)[p] == s[p]
    var p := 0;
    while p < n
        invariant 0 <= p <= n
        invariant forall q :: 0 <= q < p ==> ApplyShifts(s, n)[q] == s[q]
    {
        shift_index(s, n, p);
        // By shift_index, ApplyShifts(s,n)[p] == s[(p+n)%n] == s[p]
        p := p + 1;
    }
}

lemma shift_periodic(s: string, k: nat, t: nat)
    requires |s| > 0
    requires 0 < k <= |s|
    requires ApplyShifts(s, k) == s
    ensures ApplyShifts(s, t + k) == ApplyShifts(s, t)
{
    // ApplyShifts(s, t + k) == ApplyShifts(ApplyShifts(s,t), k) == ApplyShifts(ApplyShifts(s,k), t) == ApplyShifts(s,t)
    shift_add(s, t, k);
    shift_commute(s, t, k);
    // Using ApplyShifts(s,k) == s gives the result
}

lemma minimal_prefix_distinct(s: string, k: nat)
    requires |s| > 0
    requires 1 <= k <= |s|
    requires ApplyShifts(s, k) == s
    requires forall m :: 1 <= m < k ==> ApplyShifts(s, m) != s
    ensures forall i, j :: 0 <= i < j < k ==> ApplyShifts(s, i) != ApplyShifts(s, j)
{
    // Suppose ApplyShifts(s,i) == ApplyShifts(s,j) with i<j<k.
    // Then applying shift_periodic with parameter (k-j) to both sides yields a contradiction with minimality.
    // Formal proof by contradiction:
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall ii, jj :: 0 <= ii < jj < i ==> ApplyShifts(s, ii) != ApplyShifts(s, jj)
    {
        var j := i + 1;
        while j < k
            invariant i+1 <= j <= k
            invariant forall ii, jj :: 0 <= ii < jj < i ==> ApplyShifts(s, ii) != ApplyShifts(s, jj)
        {
            if ApplyShifts(s, i) == ApplyShifts(s, j) {
                // Then ApplyShifts(s, i + (k - j)) == ApplyShifts(s, j + (k - j)) == ApplyShifts(s, k) == s
                var diff := k - j;
                shift_add(s, i, diff);
                // ApplyShifts(s, i + diff) == ApplyShifts(ApplyShifts(s,i), diff)
                // Also ApplyShifts(s, j + diff) == ApplyShifts(ApplyShifts(s,j), diff)
                // Since ApplyShifts(s,i) == ApplyShifts(s,j), these are equal.
                // But j + diff == k, so ApplyShifts(s, k) == s, hence ApplyShifts(s, i + diff) == s
                // Note 0 < i + diff < k because i<j implies 0 < k - j <= k - (i+1) => i + diff < k
                // This contradicts minimality assumption.
                // We show contradiction by asserting the smaller period exists.
                assert 0 < i + diff < k;
                // contradiction with forall m < k, ApplyShifts(s,m) != s
                // So this branch cannot happen; loop continues
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

lemma minimal_k_set_eq(s: string, k: nat)
    requires |s| > 0
    requires 1 <= k <= |s|
    requires ApplyShifts(s, k) == s
    requires forall m :: 1 <= m < k ==> ApplyShifts(s, m) != s
    ensures |AllDistinctCyclicShifts(s)| == k
{
    // Show AllDistinctCyclicShifts(s) = set i | 0 <= i < k :: ApplyShifts(s,i)
    // First, every ApplyShifts(s,j) for 0<=j<|s| equals some ApplyShifts(s,r) with 0<=r<k
    var n := |s|;
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant forall jj :: 0 <= jj < j ==> (exists r :: 0 <= r < k && ApplyShifts(s, jj) == ApplyShifts(s, r))
    {
        if j < k {
            // take r = j
        } else {
            // j >= k, so reduce by k using periodicity repeatedly
            // we show ApplyShifts(s, j) == ApplyShifts(s, j - k)
            shift_periodic(s, k, j - k);
            // by induction on j we get existence of r < k
        }
        j := j + 1;
    }

    //
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
lemma shift_add(s: string, a: nat, b: nat)
    requires |s| > 0
    ensures ApplyShifts(s, a + b) == ApplyShifts(ApplyShifts(s, a), b)
    decreases b
{
    if b == 0 {
        // trivial
    } else {
        shift_add(s, a, b - 1);
        // ApplyShifts(s, a + b) == CyclicShiftForward(ApplyShifts(s, a + b - 1))
        // == CyclicShiftForward(ApplyShifts(ApplyShifts(s, a), b - 1))
        // == ApplyShifts(ApplyShifts(s, a), b)
    }
}

lemma shift_commute(s: string, a: nat, b: nat)
    requires |s| > 0
    ensures ApplyShifts(ApplyShifts(s, a), b) == ApplyShifts(ApplyShifts(s, b), a)
{
    // ApplyShifts(ApplyShifts(s,a),b) == ApplyShifts(s, a+b) == ApplyShifts(ApplyShifts(s,b), a)
    shift_add(s, a, b);
    shift_add(s, b, a);
}

lemma shift_index(s: string, i: nat, p: int)
    requires |s| > 0
    requires 0 <= p < |s|
    ensures ApplyShifts(s, i)[p] == s[(p + i) % |s|]
    decreases i
{
    if i == 0 {
        // ApplyShifts(s,0) == s
    } else {
        // ApplyShifts(s,i) == CyclicShiftForward(ApplyShifts(s,i-1))
        // handle indexing
        if p < |s| - 1 {
            // ApplyShifts(s,i)[p] == ApplyShifts(s,i-1)[p+1]
            shift_index(s, i - 1, p + 1);
        } else {
            // p == |s|-1
            // ApplyShifts(s,i)[|s|-1] == ApplyShifts(s,i-1)[0]
            shift_index(s, i - 1, 0);
        }
    }
}

lemma shift_n_is_identity(s: string)
    requires |s| > 0
    ensures ApplyShifts(s, |s|) == s
{
    var n := |s|;
    // Show for all positions p, ApplyShifts(s,n)[p] == s[p]
    var p := 0;
    while p < n
        invariant 0 <= p <= n
        invariant forall q :: 0 <= q < p ==> ApplyShifts(s, n)[q] == s[q]
    {
        shift_index(s, n, p);
        // By shift_index, ApplyShifts(s,n)[p] == s[(p+n)%n] == s[p]
        p := p + 1;
    }
}

lemma shift_periodic(s: string, k: nat, t: nat)
    requires |s| > 0
    requires 0 < k <= |s|
    requires ApplyShifts(s, k) == s
    ensures ApplyShifts(s, t + k) == ApplyShifts(s, t)
{
    // ApplyShifts(s, t + k) == ApplyShifts(ApplyShifts(s,t), k) == ApplyShifts(ApplyShifts(s,k), t) == ApplyShifts(s,t)
    shift_add(s, t, k);
    shift_commute(s, t, k);
    // Using ApplyShifts(s,k) == s gives the result
}

lemma minimal_prefix_distinct(s: string, k: nat)
    requires |s| > 0
    requires 1 <= k <= |s|
    requires ApplyShifts(s, k) == s
    requires forall m :: 1 <= m < k ==> ApplyShifts(s, m) != s
    ensures forall i, j :: 0 <= i < j < k ==> ApplyShifts(s, i) != ApplyShifts(s, j)
{
    // Suppose ApplyShifts(s,i) == ApplyShifts(s,j) with i<j<k.
    // Then applying shift_periodic with parameter (k-j) to both sides yields a contradiction with minimality.
    // Formal proof by contradiction:
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall ii, jj :: 0 <= ii < jj < i ==> ApplyShifts(s, ii) != ApplyShifts(s, jj)
    {
        var j := i + 1;
        while j < k
            invariant i+1 <= j <= k
            invariant forall ii, jj :: 0 <= ii < jj < i ==> ApplyShifts(s, ii) != ApplyShifts(s, jj)
        {
            if ApplyShifts(s, i) == ApplyShifts(s, j) {
                // Then ApplyShifts(s, i + (k - j)) == ApplyShifts(s, j + (k - j)) == ApplyShifts(s, k) == s
                var diff := k - j;
                shift_add(s, i, diff);
                // ApplyShifts(s, i + diff) == ApplyShifts(ApplyShifts(s,i), diff)
                // Also ApplyShifts(s, j + diff) == ApplyShifts(ApplyShifts(s,j), diff)
                // Since ApplyShifts(s,i) == ApplyShifts(s,j), these are equal.
                // But j + diff == k, so ApplyShifts(s, k) == s, hence ApplyShifts(s, i + diff) == s
                // Note 0 < i + diff < k because i<j implies 0 < k - j <= k - (i+1) => i + diff < k
                // This contradicts minimality assumption.
                // We show contradiction by asserting the smaller period exists.
                assert 0 < i + diff < k;
                // contradiction with forall m < k, ApplyShifts(s,m) != s
                // So this branch cannot happen; loop continues
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

lemma minimal_k_set_eq(s: string, k: nat)
    requires |s| > 0
    requires 1 <= k <= |s|
    requires ApplyShifts(s, k) == s
    requires forall m :: 1 <= m < k ==> ApplyShifts(s, m) != s
    ensures |AllDistinctCyclicShifts(s)| == k
{
    // Show AllDistinctCyclicShifts(s) = set i | 0 <= i < k :: ApplyShifts(s,i)
    // First, every ApplyShifts(s,j) for 0<=j<|s| equals some ApplyShifts(s,r) with 0<=r<k
    var n := |s|;
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant forall jj :: 0 <= jj < j ==> (exists r :: 0 <= r < k && ApplyShifts(s, jj) == ApplyShifts(s, r))
    {
        if j < k {
            // take r = j
        } else {
            // j >= k, so reduce by k using periodicity repeatedly
            // we show ApplyShifts(s, j) == ApplyShifts(s, j - k)
            shift_periodic(s, k, j - k);
            // by induction on j we get existence of r < k
        }
        j := j + 1;
    }

    //
// </vc-code>

