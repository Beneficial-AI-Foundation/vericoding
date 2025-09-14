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
lemma GreaterThanComparerProperties(n1: int, n2: int)
    ensures (n1 > n2) == !(n1 <= n2)
    ensures (n1 >= n2) == !(n1 < n2)
{
}

lemma SortedTransitivity(q: seq<int>, i: int, j: int, k: int)
    requires Sorted(q)
    requires 0 <= i <= j <= k < |q|
    ensures q[i] <= q[j] <= q[k]
{
}

lemma BinarySearchLeftCorrectness(q: seq<int>, key: int)
    requires Sorted(q)
    ensures forall i :: 0 <= i < |q| && q[i] < key ==> !(q[i] >= key)
    ensures forall i :: 0 <= i < |q| && q[i] >= key ==> q[i] >= key
{
}

lemma BinarySearchRightCorrectness(q: seq<int>, key: int)
    requires Sorted(q)
    ensures forall i :: 0 <= i < |q| && q[i] <= key ==> !(q[i] > key)
    ensures forall i :: 0 <= i < |q| && q[i] > key ==> q[i] > key
{
}

lemma RangeComparerEquivalence(q: seq<int>, key: int, lb: nat, ub: nat)
    requires 0 <= lb <= ub <= |q|
    ensures RangeSatisfiesComparer(q, key, lb, ub, (n1, n2) => n1 >= n2) <==> (forall i :: lb <= i < ub ==> q[i] >= key)
    ensures RangeSatisfiesComparerNegation(q, key, lb, ub, (n1, n2) => n1 >= n2) <==> (forall i :: lb <= i < ub ==> q[i] < key)
    ensures RangeSatisfiesComparer(q, key, lb, ub, (n1, n2) => n1 > n2) <==> (forall i :: lb <= i < ub ==> q[i] > key)
    ensures RangeSatisfiesComparerNegation(q, key, lb, ub, (n1, n2) => n1 > n2) <==> (forall i :: lb <= i < ub ==> q[i] <= key)
{
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
    BinarySearchLeftCorrectness(q, key);
    var leftIndex := BinarySearch(q, key, 0, |q|, (n1, n2) => n1 >= n2);
    
    BinarySearchRightCorrectness(q, key);
    var rightIndex := BinarySearch(q, key, leftIndex, |q|, (n1, n2) => n1 > n2);
    
    RangeComparerEquivalence(q, key, 0, leftIndex);
    RangeComparerEquivalence(q, key, leftIndex, |q|);
    RangeComparerEquivalence(q, key, rightIndex, |q|);
    
    return leftIndex, rightIndex;
}
// </vc-code>

