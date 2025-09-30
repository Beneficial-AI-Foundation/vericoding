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
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma BinarySearchLeftCorrectness(q: seq<int>, key: int, left: nat)
    requires Sorted(q)
    requires left <= |q|
    requires RangeSatisfiesComparerNegation(q, key, 0, left, (n1, n2) => n1 >= n2)
    requires RangeSatisfiesComparer(q, key, left, |q|, (n1, n2) => n1 >= n2)
    ensures forall i :: 0 <= i < left ==> q[i] < key
    ensures forall i :: left <= i < |q| ==> q[i] >= key
{
    forall i | 0 <= i < left
        ensures q[i] < key
    {
        assert !((n1, n2) => n1 >= n2)(q[i], key);
        assert !(q[i] >= key);
        assert q[i] < key;
    }
    
    forall i | left <= i < |q|
        ensures q[i] >= key
    {
        assert ((n1, n2) => n1 >= n2)(q[i], key);
        assert q[i] >= key;
    }
}

lemma BinarySearchRightCorrectness(q: seq<int>, key: int, right: nat)
    requires Sorted(q)
    requires right <= |q|
    requires RangeSatisfiesComparerNegation(q, key, 0, right, (n1, n2) => n1 > n2)
    requires RangeSatisfiesComparer(q, key, right, |q|, (n1, n2) => n1 > n2)
    ensures forall i :: 0 <= i < right ==> q[i] <= key
    ensures forall i :: right <= i < |q| ==> q[i] > key
{
    forall i | 0 <= i < right
        ensures q[i] <= key
    {
        assert !((n1, n2) => n1 > n2)(q[i], key);
        assert !(q[i] > key);
        assert q[i] <= key;
    }
    
    forall i | right <= i < |q|
        ensures q[i] > key
    {
        assert ((n1, n2) => n1 > n2)(q[i], key);
        assert q[i] > key;
    }
}

lemma CombinedRangeCorrectness(q: seq<int>, key: int, left: nat, right: nat)
    requires Sorted(q)
    requires left <= right <= |q|
    requires forall i :: 0 <= i < left ==> q[i] < key
    requires forall i :: left <= i < |q| ==> q[i] >= key
    requires forall i :: 0 <= i < right ==> q[i] <= key
    requires forall i :: right <= i < |q| ==> q[i] > key
    ensures forall i :: left <= i < right ==> q[i] == key
{
    forall i | left <= i < right
        ensures q[i] == key
    {
        assert q[i] >= key;
        assert q[i] <= key;
    }
}
// </vc-helpers>

// <vc-spec>
method FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
    requires Sorted(q)
    ensures left <= right <= |q|
    ensures forall i :: 0 <= i < left ==> q[i] < key
    ensures forall i :: left <= i < right ==> q[i] == key
    ensures forall i :: right <= i < |q| ==> q[i] > key
// </vc-spec>
// <vc-code>
{
    left := BinarySearch(q, key, 0, |q|, (n1, n2) => n1 >= n2);
    assert RangeSatisfiesComparerNegation(q, key, 0, left, (n1, n2) => n1 >= n2);
    assert RangeSatisfiesComparer(q, key, left, |q|, (n1, n2) => n1 >= n2);
    BinarySearchLeftCorrectness(q, key, left);
    
    right := BinarySearch(q, key, 0, |q|, (n1, n2) => n1 > n2);
    assert RangeSatisfiesComparerNegation(q, key, 0, right, (n1, n2) => n1 > n2);
    assert RangeSatisfiesComparer(q, key, right, |q|, (n1, n2) => n1 > n2);
    BinarySearchRightCorrectness(q, key, right);
    
    assert left <= right by {
        if left > right {
            assert left > 0 by {
                if left == 0 {
                    assert false;
                }
            }
            assert q[left-1] < key;
            assert q[left-1] > key;
            assert false;
        }
    }
    
    CombinedRangeCorrectness(q, key, left, right);
}
// </vc-code>

