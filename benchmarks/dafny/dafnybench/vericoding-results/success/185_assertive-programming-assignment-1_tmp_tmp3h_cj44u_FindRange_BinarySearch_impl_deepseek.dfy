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
lemma lemma_LessThanOrEqualImpliesLessThanOrEqual(n1: int, n2: int, n3: int)
  requires n1 <= n2
  requires n2 <= n3
  ensures n1 <= n3
{
}

lemma lemma_ComparerImpliesGreaterOrEqual(q: seq<int>, key: int, i: nat, comparer: (int, int) -> bool)
  requires 0 <= i < |q|
  requires comparer(q[i], key)
  requires (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) || (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
  ensures q[i] >= key
{
  if forall n1, n2 :: comparer(n1, n2) == (n1 > n2) {
    assert q[i] > key;
  } else if forall n1, n2 :: comparer(n1, n2) == (n1 >= n2) {
    assert q[i] >= key;
  }
}

lemma lemma_TransitivityForGreaterEqual(q: seq<int>, key: int, i: nat, j: nat)
  requires Sorted(q)
  requires 0 <= i <= j < |q|
  requires q[j] >= key
  ensures q[i] <= key || q[i] >= key
{
}

lemma lemma_MidBounds(low: nat, high: nat, lowerBound: nat, upperBound: nat)
  requires lowerBound <= low <= high <= upperBound
  requires low < high
  ensures lowerBound <= (low + high) / 2 < upperBound
{
}

lemma lemma_SortedPreservation(q: seq<int>, i: nat, j: nat)
  requires Sorted(q)
  requires 0 <= i <= j < |q|
  ensures q[i] <= q[j]
{
}

lemma lemma_RangeSatisfiesComparerExtension(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
  requires Sorted(q)
  requires 0 <= lowerBound <= upperBound <= |q|
  requires RangeSatisfiesComparer(q, key, upperBound, |q|, comparer)
  requires (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) || (forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))
  ensures forall i :: upperBound <= i < |q| ==> comparer(q[i], key)
{
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
    var mid := (low + high) / 2;
    
    if comparer(q[mid], key) {
      high := mid;
      // Prove that RangeSatisfiesComparer(q, key, high, |q|, comparer) still holds
      lemma_ComparerImpliesGreaterOrEqual(q, key, mid, comparer);
      if forall n1, n2 :: comparer(n1, n2) == (n1 > n2) {
        assert q[mid] > key;
        // Since q is sorted, all elements from mid onward are >= q[mid] > key
        forall j | high <= j < |q| ensures comparer(q[j], key) {
          lemma_SortedPreservation(q, mid, j);
          assert q[j] >= q[mid] > key;
        }
      } else if forall n1, n2 :: comparer(n1, n2) == (n1 >= n2) {
        assert q[mid] >= key;
        // Since q is sorted, all elements from mid onward are >= q[mid] >= key
        forall j | high <= j < |q| ensures comparer(q[j], key) {
          lemma_SortedPreservation(q, mid, j);
          assert q[j] >= q[mid] >= key;
        }
      }
    } else {
      low := mid + 1;
      // Prove that RangeSatisfiesComparerNegation(q, key, 0, low, comparer) still holds
      // !comparer(q[mid], key) means either q[mid] <= key (for >=) or q[mid] <= key (for >)
      if forall n1, n2 :: comparer(n1, n2) == (n1 > n2) {
        assert q[mid] <= key;
        // Since q is sorted, all elements before mid+1 are <= q[mid] <= key
        forall i | 0 <= i < low ensures !comparer(q[i], key) {
          lemma_SortedPreservation(q, i, mid);
          assert q[i] <= q[mid] <= key;
        }
      } else if forall n1, n2 :: comparer(n1, n2) == (n1 >= n2) {
        assert q[mid] < key;
        // Since q is sorted, all elements before mid+1 are <= q[mid] < key
        forall i | 0 <= i < low ensures !comparer(q[i], key) {
          lemma_SortedPreservation(q, i, mid);
          assert q[i] <= q[mid] < key;
        }
      }
    }
  }
  
  index := low;
}
// </vc-code>

