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
lemma ComparerTransitivity(q: seq<int>, key: int, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
             (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    ensures forall i, j :: 0 <= i <= j < |q| && comparer(q[i], key) ==> comparer(q[j], key)
{
    forall i, j | 0 <= i <= j < |q| && comparer(q[i], key)
        ensures comparer(q[j], key)
    {
        assert q[i] <= q[j];
        if forall n1, n2 :: comparer(n1, n2) == (n1 > n2) {
            if q[i] > key {
                assert q[j] >= q[i] > key;
                assert q[j] > key;
            }
        } else {
            assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
            if q[i] >= key {
                assert q[j] >= q[i] >= key;
                assert q[j] >= key;
            }
        }
    }
}

lemma ComparerNegationTransitivity(q: seq<int>, key: int, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
             (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    ensures forall i, j :: 0 <= i <= j < |q| && !comparer(q[j], key) ==> !comparer(q[i], key)
{
    forall i, j | 0 <= i <= j < |q| && !comparer(q[j], key)
        ensures !comparer(q[i], key)
    {
        assert q[i] <= q[j];
        if forall n1, n2 :: comparer(n1, n2) == (n1 > n2) {
            if q[j] <= key {
                assert q[i] <= q[j] <= key;
                assert q[i] <= key;
                assert !(q[i] > key);
            }
        } else {
            assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
            if q[j] < key {
                assert q[i] <= q[j] < key;
                assert q[i] < key;
                assert !(q[i] >= key);
            }
        }
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
        decreases high - low
    {
        var mid := (low + high) / 2;
        assert low <= mid < high;
        
        if comparer(q[mid], key) {
            ComparerTransitivity(q, key, comparer);
            assert forall i :: mid <= i < |q| ==> comparer(q[i], key);
            high := mid;
        } else {
            ComparerNegationTransitivity(q, key, comparer);
            assert forall i :: 0 <= i <= mid ==> !comparer(q[i], key);
            low := mid + 1;
        }
    }
    
    index := low;
}
// </vc-code>

