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
lemma RangeSatisfiesComparer_Monotone(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, c1: (int, int) -> bool, c2: (int, int) -> bool)
  requires 0 <= lowerBound <= upperBound <= |q|
  requires forall x: int, y: int :: c1(x, y) ==> c2(x, y)
  requires RangeSatisfiesComparer(q, key, lowerBound, upperBound, c1)
  ensures RangeSatisfiesComparer(q, key, lowerBound, upperBound, c2)
{
  assert forall i :: lowerBound <= i < upperBound ==> c2(q[i], key) by {
    forall i | lowerBound <= i < upperBound
      ensures c2(q[i], key)
    {
      assert c1(q[i], key);
      assert c1(q[i], key) ==> c2(q[i], key);
    }
  }
}

lemma BoundaryOrder(q: seq<int>, key: int, a: nat, b: nat, comparer: (int, int) -> bool)
  requires 0 <= a <= |q|
  requires 0 <= b <= |q|
  requires RangeSatisfiesComparerNegation(q, key, 0, a, comparer)
  requires RangeSatisfiesComparer(q, key, b, |q|, comparer)
  ensures a <= b
{
  if a > b {
    assert 0 <= b < a;
    assert b < |q|;
    assert !comparer(q[b], key);
    assert comparer(q[b], key);
    assert false;
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
  var ge: (int, int) -> bool := (n1: int, n2: int) => n1 >= n2;
  var gt: (int, int) -> bool := (n1: int, n2: int) => n1 > n2;

  left := BinarySearch(q, key, 0, |q|, ge);
  right := BinarySearch(q, key, 0, |q|, gt);

  assert forall n1: int, n2: int :: gt(n1, n2) ==> ge(n1, n2);
  RangeSatisfiesComparer_Monotone(q, key, right, |q|, gt, ge);
  BoundaryOrder(q, key, left, right, ge);

  assert forall i :: 0 <= i < left ==> q[i] < key by {
    forall i | 0 <= i < left
      ensures q[i] < key
    {
      assert !ge(q[i], key);
      assert q[i] < key;
    }
  }

  assert forall i :: left <= i < right ==> q[i] == key by {
    forall i | left <= i < right
      ensures q[i] == key
    {
      assert ge(q[i], key);
      assert !gt(q[i], key);
      assert q[i] >= key;
      assert !(q[i] > key);
      assert q[i] <= key;
      assert q[i] == key;
    }
  }
}
// </vc-code>

