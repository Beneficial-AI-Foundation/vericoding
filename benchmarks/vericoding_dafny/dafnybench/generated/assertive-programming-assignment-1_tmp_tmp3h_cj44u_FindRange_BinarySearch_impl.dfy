// <vc-helpers>
predicate Sorted(q: seq<int>) {
    forall i, j :: 0 <= i < j < |q| ==> q[i] <= q[j]
}

predicate RangeSatisfiesComparerNegation(q: seq<int>, key: int, start: int, end: int, comparer: (int, int) -> bool) 
    requires 0 <= start <= end <= |q|
{
    forall i :: start <= i < end ==> !comparer(q[i], key)
}

predicate RangeSatisfiesComparer(q: seq<int>, key: int, start: int, end: int, comparer: (int, int) -> bool)
    requires 0 <= start <= end <= |q|
{
    forall i :: start <= i < end ==> comparer(q[i], key)
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool) returns (index: nat)
    requires Sorted(q)
    requires 0 <= lowerBound <= upperBound <= |q|
    requires RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer)
    requires RangeSatisfiesComparer(q, key, upperBound, |q|, comparer)
    // comparer is '>' or '>='
    requires
        (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
        (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))

    ensures lowerBound <= index <= upperBound
    ensures RangeSatisfiesComparerNegation(q, key, 0, index, comparer)
    ensures RangeSatisfiesComparer(q, key, index, |q|, comparer)
// </vc-spec>
// <vc-code>
{
    var low := lowerBound;
    var high := upperBound;
    
    while low < high
        invariant lowerBound <= low <= high <= upperBound
        invariant RangeSatisfiesComparerNegation(q, key, 0, low, comparer)
        invariant RangeSatisfiesComparer(q, key, high, |q|, comparer)
        decreases high - low
    {
        var mid := (low + high) / 2;
        
        if comparer(q[mid], key) {
            high := mid;
        } else {
            low := mid + 1;
        }
    }
    
    index := low;
}
// </vc-code>