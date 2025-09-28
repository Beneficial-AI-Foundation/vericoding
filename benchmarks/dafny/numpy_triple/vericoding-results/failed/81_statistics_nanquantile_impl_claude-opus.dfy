// <vc-preamble>
// Custom datatype to represent float values that can be NaN
datatype FloatValue = NaN | Value(val: real)

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
    f.NaN?
}

// Predicate to check if there exists at least one non-NaN value in the sequence
predicate HasNonNaNValue(a: seq<FloatValue>) {
    exists i :: 0 <= i < |a| && !IsNaN(a[i])
}

// Predicate to check if all values in the sequence are NaN
predicate AllNaN(a: seq<FloatValue>) {
    forall i :: 0 <= i < |a| ==> IsNaN(a[i])
}

// Function to get all non-NaN values from the sequence
function GetNonNaNValues(a: seq<FloatValue>): seq<real>
{
    if |a| == 0 then []
    else if IsNaN(a[0]) then GetNonNaNValues(a[1..])
    else [a[0].val] + GetNonNaNValues(a[1..])
}

// Predicate to check if a value is the minimum among non-NaN elements
predicate IsMinOfNonNaN(a: seq<FloatValue>, result: FloatValue)
    requires HasNonNaNValue(a)
{
    !IsNaN(result) &&
    (exists i :: 0 <= i < |a| && !IsNaN(a[i]) && result.val == a[i].val &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> result.val <= a[j].val))
}

// Predicate to check if a value is the maximum among non-NaN elements
predicate IsMaxOfNonNaN(a: seq<FloatValue>, result: FloatValue)
    requires HasNonNaNValue(a)
{
    !IsNaN(result) &&
    (exists i :: 0 <= i < |a| && !IsNaN(a[i]) && result.val == a[i].val &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> a[j].val <= result.val))
}

// Predicate to check if result is bounded by non-NaN elements
predicate IsBoundedByNonNaN(a: seq<FloatValue>, result: FloatValue)
    requires HasNonNaNValue(a)
{
    !IsNaN(result) &&
    (exists min_i :: 0 <= min_i < |a| && !IsNaN(a[min_i]) &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> a[min_i].val <= a[j].val) &&
        a[min_i].val <= result.val) &&
    (exists max_i :: 0 <= max_i < |a| && !IsNaN(a[max_i]) &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> a[j].val <= a[max_i].val) &&
        result.val <= a[max_i].val)
}

/**
 * Computes the q-th quantile of the data in a sequence, ignoring NaN values.
 * When all elements are NaN, returns NaN.
 * 
 * @param a: Input sequence of FloatValues (may contain NaN)
 * @param q: Quantile parameter, must be between 0.0 and 1.0 inclusive
 * @returns: The q-th quantile of non-NaN values, or NaN if all values are NaN
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sorting function postconditions and partition properties */
function MinOfNonNaN(a: seq<FloatValue>): FloatValue
    requires HasNonNaNValue(a)
    ensures IsMinOfNonNaN(a, MinOfNonNaN(a))
    decreases |a|
{
    if |a| == 1 then
        a[0]
    else if IsNaN(a[0]) then
        assert HasNonNaNValue(a[1..]);
        MinOfNonNaN(a[1..])
    else if HasNonNaNValue(a[1..]) then
        var rest := MinOfNonNaN(a[1..]);
        if a[0].val <= rest.val then a[0] else rest
    else
        a[0]
}

function MaxOfNonNaN(a: seq<FloatValue>): FloatValue
    requires HasNonNaNValue(a)
    ensures IsMaxOfNonNaN(a, MaxOfNonNaN(a))
    decreases |a|
{
    if |a| == 1 then
        a[0]
    else if IsNaN(a[0]) then
        assert HasNonNaNValue(a[1..]);
        MaxOfNonNaN(a[1..])
    else if HasNonNaNValue(a[1..]) then
        var rest := MaxOfNonNaN(a[1..]);
        if a[0].val >= rest.val then a[0] else rest
    else
        a[0]
}

function ComputeQuantile(sorted: seq<real>, q: real): real
    requires |sorted| > 0
    requires 0.0 <= q <= 1.0
    requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
    if q == 0.0 then sorted[0]
    else if q == 1.0 then sorted[|sorted| - 1]
    else if |sorted| == 1 then sorted[0]
    else
        var pos := q * (|sorted| - 1) as real;
        var lower := pos.Floor;
        var upper := lower + 1;
        if upper >= |sorted| then sorted[|sorted| - 1]
        else if lower < 0 then sorted[0]
        else
            var weight := pos - lower as real;
            sorted[lower] as real * (1.0 - weight) + sorted[upper] as real * weight
}

function SortedNonNaN(a: seq<FloatValue>): seq<real>
{
    var nonNaN := GetNonNaNValues(a);
    SortSeq(nonNaN)
}

function FilterLess(s: seq<real>, pivot: real): seq<real>
    ensures forall x :: x in FilterLess(s, pivot) ==> x in s && x < pivot
    ensures forall x :: x in s && x < pivot ==> x in FilterLess(s, pivot)
    ensures |FilterLess(s, pivot)| <= |s|
{
    if |s| == 0 then []
    else if s[0] < pivot then [s[0]] + FilterLess(s[1..], pivot)
    else FilterLess(s[1..], pivot)
}

function FilterEqual(s: seq<real>, pivot: real): seq<real>
    ensures forall x :: x in FilterEqual(s, pivot) ==> x in s && x == pivot
    ensures forall x :: x in s && x == pivot ==> x in FilterEqual(s, pivot)
    ensures pivot in s ==> |FilterEqual(s, pivot)| >= 1
{
    if |s| == 0 then []
    else if s[0] == pivot then [s[0]] + FilterEqual(s[1..], pivot)
    else FilterEqual(s[1..], pivot)
}

function FilterGreater(s: seq<real>, pivot: real): seq<real>
    ensures forall x :: x in FilterGreater(s, pivot) ==> x in s && x > pivot
    ensures forall x :: x in s && x > pivot ==> x in FilterGreater(s, pivot)
    ensures |FilterGreater(s, pivot)| <= |s|
{
    if |s| == 0 then []
    else if s[0] > pivot then [s[0]] + FilterGreater(s[1..], pivot)
    else FilterGreater(s[1..], pivot)
}

lemma ConcatSorted(left: seq<real>, mid: seq<real>, right: seq<real>)
    requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
    requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
    requires forall x :: x in left ==> forall y :: y in mid ==> x < y
    requires forall x :: x in mid ==> forall y :: y in right ==> x < y
    requires forall x :: x in left ==> forall y :: y in right ==> x < y
    requires forall x, y :: x in mid && y in mid ==> x == y
    ensures forall i, j :: 0 <= i < j < |left + mid + right| ==> (left + mid + right)[i] <= (left + mid + right)[j]
{
}

function SortSeq(s: seq<real>): seq<real>
    ensures |SortSeq(s)| == |s|
    ensures multiset(SortSeq(s)) == multiset(s)
    ensures forall i, j :: 0 <= i < j < |SortSeq(s)| ==> SortSeq(s)[i] <= SortSeq(s)[j]
    decreases |s|
{
    if |s| == 0 then
        []
    else if |s| == 1 then
        s
    else
        var pivot := s[|s|/2];
        var left := FilterLess(s, pivot);
        var equal := FilterEqual(s, pivot);
        var right := FilterGreater(s, pivot);
        assert pivot in s;
        assert |equal| >= 1;
        assert |left| < |s| by {
            if |left| == |s| {
                assert forall x :: x in s ==> x < pivot;
                assert pivot in s;
                assert false;
            }
        }
        assert |right| < |s| by {
            if |right| == |s| {
                assert forall x :: x in s ==> x > pivot;
                assert pivot in s;
                assert false;
            }
        }
        var sortedLeft := SortSeq(left);
        var sortedRight := SortSeq(right);
        ConcatSorted(sortedLeft, equal, sortedRight);
        sortedLeft + equal + sortedRight
}
// </vc-helpers>

// <vc-spec>
method nanquantile(a: seq<FloatValue>, q: real) returns (result: FloatValue)
    requires 0.0 <= q <= 1.0  // Quantile parameter must be valid
    requires |a| > 0           // Input sequence must be non-empty
    ensures
        // Case 1: If there exists at least one non-NaN element
        HasNonNaNValue(a) ==> 
            (IsBoundedByNonNaN(a, result) &&
             // For q=0, result is the minimum of non-NaN elements
             (q == 0.0 ==> IsMinOfNonNaN(a, result)) &&
             // For q=1, result is the maximum of non-NaN elements  
             (q == 1.0 ==> IsMaxOfNonNaN(a, result)))
    ensures
        // Case 2: If all elements are NaN, result is NaN
        AllNaN(a) ==> IsNaN(result)
    ensures
        // Case 3: For sequences without NaN, result is properly bounded
        (!exists i :: 0 <= i < |a| && IsNaN(a[i])) ==> 
            (!IsNaN(result) &&
             exists lower_i, upper_i :: 
                0 <= lower_i < |a| && 0 <= upper_i < |a| &&
                a[lower_i].val <= result.val <= a[upper_i].val)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified implementation to avoid verification timeout */
    if AllNaN(a) {
        result := NaN;
    } else {
        assert HasNonNaNValue(a);
        if q == 0.0 {
            result := MinOfNonNaN(a);
        } else if q == 1.0 {
            result := MaxOfNonNaN(a);
        } else {
            var nonNaNValues := GetNonNaNValues(a);
            assert |nonNaNValues| > 0;
            var sorted := SortSeq(nonNaNValues);
            var quantileValue := ComputeQuantile(sorted, q);
            result := Value(quantileValue);
        }
    }
}
// </vc-code>
