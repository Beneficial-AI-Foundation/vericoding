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
lemma ComparerTransitivity(q: seq<int>, key: int, comparer: (int, int) -> bool, i: int, j: int)
    requires Sorted(q)
    requires 0 <= i <= j < |q|
    requires (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) || (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    requires comparer(q[i], key)
    ensures comparer(q[j], key)
{
    if forall n1, n2 :: comparer(n1, n2) == (n1 >  n2) {
        assert q[i] <= q[j];
        assert q[i] > key;
        assert q[j] >= q[i] > key;
        assert q[j] > key;
        assert comparer(q[j], key);
    } else {
        assert q[i] <= q[j];
        assert q[i] >= key;
        assert q[j] >= q[i] >= key;
        assert q[j] >= key;
        assert comparer(q[j], key);
    }
}

lemma ComparerNegationTransitivity(q: seq<int>, key: int, comparer: (int, int) -> bool, i: int, j: int)
    requires Sorted(q)
    requires 0 <= i <= j < |q|
    requires (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) || (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    requires !comparer(q[j], key)
    ensures !comparer(q[i], key)
{
    if forall n1, n2 :: comparer(n1, n2) == (n1 >  n2) {
        assert q[i] <= q[j];
        assert !(q[j] > key);
        assert q[j] <= key;
        assert q[i] <= q[j] <= key;
        assert !(q[i] > key);
        assert !comparer(q[i], key);
    } else {
        assert q[i] <= q[j];
        assert !(q[j] >= key);
        assert q[j] < key;
        assert q[i] <= q[j] < key;
        assert !(q[i] >= key);
        assert !comparer(q[i], key);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    var lo := lowerBound;
    var hi := upperBound;
    
    while lo < hi
        invariant lowerBound <= lo <= hi <= upperBound
        invariant RangeSatisfiesComparerNegation(q, key, 0, lo, comparer)
        invariant RangeSatisfiesComparer(q, key, hi, |q|, comparer)
    {
        var mid := (lo + hi) / 2;
        assert lo <= mid < hi;
        
        if comparer(q[mid], key) {
            forall i | 0 <= i < lo
                ensures !comparer(q[i], key)
            {
                assert RangeSatisfiesComparerNegation(q, key, 0, lo, comparer);
            }
            
            forall i | mid <= i < |q|
                ensures comparer(q[i], key)
            {
                if i >= hi {
                    assert RangeSatisfiesComparer(q, key, hi, |q|, comparer);
                } else {
                    ComparerTransitivity(q, key, comparer, mid, i);
                }
            }
            
            hi := mid;
        } else {
            forall i | 0 <= i <= mid
                ensures !comparer(q[i], key)
            {
                if i < lo {
                    assert RangeSatisfiesComparerNegation(q, key, 0, lo, comparer);
                } else {
                    ComparerNegationTransitivity(q, key, comparer, i, mid);
                }
            }
            
            forall i | hi <= i < |q|
                ensures comparer(q[i], key)
            {
                assert RangeSatisfiesComparer(q, key, hi, |q|, comparer);
            }
            
            lo := mid + 1;
        }
    }
    
    index := lo;
}
// </vc-code>
