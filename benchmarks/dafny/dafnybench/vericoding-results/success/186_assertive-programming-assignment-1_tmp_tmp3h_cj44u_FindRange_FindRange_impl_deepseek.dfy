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
lemma LemmaRangeSatisfiesComparerTransitive(q: seq<int>, key: int, a: nat, b: nat, c: nat, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires 0 <= a <= b <= c <= |q|
    requires RangeSatisfiesComparer(q, key, a, b, comparer)
    requires RangeSatisfiesComparer(q, key, b, c, comparer)
    ensures RangeSatisfiesComparer(q, key, a, c, comparer)
{
}

lemma LemmaRangeSatisfiesComparerNegationTransitive(q: seq<int>, key: int, a: nat, b: nat, c: nat, comparer: (int, int) -> bool)
    requires Sorted(q)
    requires 0 <= a <= b <= c <= |q|
    requires RangeSatisfiesComparerNegation(q, key, a, b, comparer)
    requires RangeSatisfiesComparerNegation(q, key, b, c, comparer)
    ensures RangeSatisfiesComparerNegation(q, key, a, c, comparer)
{
}

lemma LemmaBinarySearchProperties(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool, index: nat)
    requires Sorted(q)
    requires 0 <= lowerBound <= upperBound <= |q|
    requires RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer)
    requires RangeSatisfiesComparer(q, key, upperBound, |q|, comparer)
    requires (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) || (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
    requires lowerBound <= index <= upperBound
    requires RangeSatisfiesComparerNegation(q, key, 0, index, comparer)
    requires RangeSatisfiesComparer(q, key, index, |q|, comparer)
    ensures index == lowerBound ==> (lowerBound < |q| ==> comparer(q[lowerBound], key)) || lowerBound == upperBound
    ensures index == upperBound ==> (upperBound > 0 ==> !comparer(q[upperBound - 1], key)) || lowerBound == upperBound
{
}

predicate GreaterEqualComparer(n1: int, n2: int) {
    n1 >= n2
}

predicate GreaterComparer(n1: int, n2: int) {
    n1 > n2
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
  var low := 0;
  var high := |q|;
  
  var leftIndex := BinarySearch(q, key, low, high, GreaterEqualComparer);
  var rightIndex := BinarySearch(q, key, low, high, GreaterComparer);
  
  if leftIndex == high || (leftIndex < |q| && q[leftIndex] != key) {
    left := leftIndex;
    right := leftIndex;
  } else {
    left := leftIndex;
    right := rightIndex;
  }
}
// </vc-code>

