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
lemma ComparerMonotoneRight(q: seq<int>, key: int, i: nat, j: nat, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires i <= j < |q|
    requires
        (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
        (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    ensures comparer(q[i], key) ==> comparer(q[j], key)
{
    if (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) {
        if comparer(q[i], key) {
            assert comparer(q[i], key) == (q[i] > key);
            assert q[i] > key;
            assert 0 <= i <= j < |q|;
            assert q[i] <= q[j];
            assert key < q[i];
            assert key < q[j];
            assert comparer(q[j], key);
        }
    } else {
        assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
        if comparer(q[i], key) {
            assert comparer(q[i], key) == (q[i] >= key);
            assert q[i] >= key;
            assert 0 <= i <= j < |q|;
            assert q[i] <= q[j];
            assert q[j] >= key;
            assert comparer(q[j], key);
        }
    }
}

lemma ComparerMonotoneLeftNeg(q: seq<int>, key: int, j: nat, i: nat, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires j <= i < |q|
    requires
        (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
        (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    ensures !comparer(q[i], key) ==> !comparer(q[j], key)
{
    if (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) {
        if !comparer(q[i], key) {
            assert comparer(q[i], key) == (q[i] > key);
            assert !(q[i] > key);
            assert q[i] <= key;
            assert 0 <= j <= i < |q|;
            assert q[j] <= q[i];
            assert q[j] <= key;
            assert !(q[j] > key);
            assert !comparer(q[j], key);
        }
    } else {
        assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
        if !comparer(q[i], key) {
            assert comparer(q[i], key) == (q[i] >= key);
            assert !(q[i] >= key);
            assert q[i] < key;
            assert 0 <= j <= i < |q|;
            assert q[j] <= q[i];
            assert q[j] < key;
            assert !(q[j] >= key);
            assert !comparer(q[j], key);
        }
    }
}

lemma TrueAtIndexImpliesSuffix(q: seq<int>, key: int, i: nat, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires i < |q|
    requires comparer(q[i], key)
    requires
        (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
        (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    ensures RangeSatisfiesComparer(q, key, i, |q|, comparer)
{
    forall j:nat
        | i <= j < |q|
        ensures comparer(q[j], key)
    {
        if (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) {
            assert comparer(q[i], key) == (q[i] > key);
            assert q[i] > key;
            assert i <= j < |q|;
            assert 0 <= i <= j < |q|;
            assert q[i] <= q[j];
            assert key < q[i];
            assert key < q[j];
            assert comparer(q[j], key);
        } else {
            assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
            assert comparer(q[i], key) == (q[i] >= key);
            assert q[i] >= key;
            assert i <= j < |q|;
            assert 0 <= i <= j < |q|;
            assert q[i] <= q[j];
            assert q[j] >= key;
            assert comparer(q[j], key);
        }
    }
}

lemma FalseAtIndexImpliesPrefix(q: seq<int>, key: int, i: nat, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires i < |q|
    requires !comparer(q[i], key)
    requires
        (forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
        (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    ensures RangeSatisfiesComparerNegation(q, key, 0, i+1, comparer)
{
    forall j:nat
        | j < i + 1
        ensures !comparer(q[j], key)
    {
        assert j <= i;
        if (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) {
            assert comparer(q[i], key) == (q[i] > key);
            assert !(q[i] > key);
            assert q[i] <= key;
            assert 0 <= j <= i < |q|;
            assert q[j] <= q[i];
            assert q[j] <= key;
            assert !(q[j] > key);
            assert !comparer(q[j], key);
        } else {
            assert forall n1, n2 :: comparer(n1, n2) == (n1 >= n2);
            assert comparer(q[i], key) == (q[i] >= key);
            assert !(q[i] >= key);
            assert q[i] < key;
            assert 0 <= j <= i < |q|;
            assert q[j] <= q[i];
            assert q[j] < key;
            assert !(q[j] >= key);
            assert !comparer(q[j], key);
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
        invariant 0 <= low <= high <= |q|
        invariant lowerBound <= low
        invariant high <= upperBound
        invariant RangeSatisfiesComparerNegation(q, key, 0, low, comparer)
        invariant RangeSatisfiesComparer(q, key, high, |q|, comparer)
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        assert low <= mid < high;
        assert mid < |q|;
        if comparer(q[mid], key) {
            TrueAtIndexImpliesSuffix(q, key, mid, comparer);
            high := mid;
        } else {
            FalseAtIndexImpliesPrefix(q, key, mid, comparer);
            low := mid + 1;
        }
    }
    index := low;
}
// </vc-code>

