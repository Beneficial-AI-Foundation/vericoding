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
// No helpers needed for this proof.
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
  var i := 0;
  // find first index i with q[i] >= key (or i == |q|)
  while i < |q| && q[i] < key
    invariant 0 <= i <= |q|
    invariant forall t :: 0 <= t < i ==> q[t] < key
  {
    i := i + 1;
  }
  left := i;
  // at this point either left == |q| or q[left] >= key
  if left < |q| {
    assert q[left] >= key;
  }

  var j := left;
  // advance j while elements equal key
  while j < |q| && q[j] == key
    invariant left <= j <= |q|
    invariant forall t :: left <= t < j ==> q[t] == key
    invariant forall t :: 0 <= t < left ==> q[t] < key
  {
    j := j + 1;
  }
  right := j;

  // now prove postconditions if needed (Dafny should discharge them)
  // ensure elements at and after right are > key when right < |q|
  if right < |q| {
    // q[right] != key and right >= left, and q[left] >= key, so q[right] > key
    assert q[right] != key;
    assert left == |q| || q[left] >= key;
    if left < |q| {
      // sorted implies q[right] >= q[left]
      assert forall a,b :: 0 <= a <= b < |q| ==> q[a] <= q[b];
      // The above is just a tautology of Sorted; Dafny uses the predicate Sorted(q).
    }
  }
}
// </vc-code>

