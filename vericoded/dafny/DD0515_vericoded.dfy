predicate Sorted(q: seq<int>)
{
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


// all the values in the range satisfy `comparer` (comparer(q[i], key) == true)
predicate RangeSatisfiesComparer(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
    requires 0 <= lowerBound <= upperBound <= |q|
{
    forall i :: lowerBound <= i < upperBound ==> comparer(q[i], key)
}

// all the values in the range satisfy `!comparer` (comparer(q[i], key) == false)
predicate RangeSatisfiesComparerNegation(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
    requires 0 <= lowerBound <= upperBound <= |q|
{
    RangeSatisfiesComparer(q, key, lowerBound, upperBound, (n1, n2) => !comparer(n1, n2))
}

// <vc-helpers>
lemma ComparerMonotonic(q: seq<int>, key: int, comparer: (int, int) -> bool, i: int, j: int)
    requires Sorted(q)
    requires 0 <= i <= j < |q|
    requires (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) || 
             (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    requires comparer(q[i], key)
    ensures comparer(q[j], key)
{
    assert q[i] <= q[j];
    if forall n1, n2 :: comparer(n1, n2) == (n1 > n2) {
        assert comparer(q[i], key) == (q[i] > key);
        assert q[i] > key;
        assert q[j] >= q[i];
        assert q[j] > key;
        assert comparer(q[j], key);
    } else {
        assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
        assert comparer(q[i], key) == (q[i] >= key);
        assert q[i] >= key;
        assert q[j] >= q[i];
        assert q[j] >= key;
        assert comparer(q[j], key);
    }
}

lemma ComparerMonotonicNegation(q: seq<int>, key: int, comparer: (int, int) -> bool, i: int, j: int)
    requires Sorted(q)
    requires 0 <= i <= j < |q|
    requires (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) || 
             (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    requires !comparer(q[j], key)
    ensures !comparer(q[i], key)
{
    assert q[i] <= q[j];
    if forall n1, n2 :: comparer(n1, n2) == (n1 > n2) {
        assert !comparer(q[j], key) == !(q[j] > key);
        assert q[j] <= key;
        assert q[i] <= q[j];
        assert q[i] <= key;
        assert !comparer(q[i], key);
    } else {
        assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
        assert !comparer(q[j], key) == !(q[j] >= key);
        assert q[j] < key;
        assert q[i] <= q[j];
        assert q[i] < key;
        assert !comparer(q[i], key);
    }
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
    {
        var mid := low + (high - low) / 2;
        assert low <= mid < high;
        
        if comparer(q[mid], key) {
            // q[mid] satisfies comparer, so all elements >= mid satisfy it
            forall i | mid <= i < |q|
                ensures comparer(q[i], key)
            {
                if i < high {
                    if mid < i {
                        ComparerMonotonic(q, key, comparer, mid, i);
                    }
                } else {
                    assert RangeSatisfiesComparer(q, key, high, |q|, comparer);
                    assert i >= high;
                    assert comparer(q[i], key);
                }
            }
            high := mid;
        } else {
            // q[mid] doesn't satisfy comparer, so all elements <= mid don't satisfy it
            forall i | 0 <= i <= mid
                ensures !comparer(q[i], key)
            {
                if i < low {
                    assert RangeSatisfiesComparerNegation(q, key, 0, low, comparer);
                    assert !comparer(q[i], key);
                } else {
                    assert low <= i <= mid;
                    ComparerMonotonicNegation(q, key, comparer, i, mid);
                }
            }
            low := mid + 1;
        }
    }
    
    index := low;
}
// </vc-code>

