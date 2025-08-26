predicate Sorted(q: seq<int>)
{
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
    exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

// <vc-helpers>
lemma PreservesAddendsWhenSumSmall(q: seq<int>, x: int, i: nat, j: nat)
    requires Sorted(q)
    requires 0 <= i < j < |q|
    requires q[i] + q[j] < x
    requires exists i0, j0 :: i <= i0 < j0 <= j && q[i0] + q[j0] == x
    ensures exists i0, j0 :: i+1 <= i0 < j0 <= j && q[i0] + q[j0] == x
{
    var i0, j0 :| i <= i0 < j0 <= j && q[i0] + q[j0] == x;
    if i0 == i {
        // q[i] + q[j0] == x, but q[i] + q[j] < x and j0 <= j
        // Since sorted, q[j0] <= q[j], so q[i] + q[j0] <= q[i] + q[j] < x
        // This contradicts q[i] + q[j0] == x
        assert q[j0] <= q[j];
        assert q[i] + q[j0] <= q[i] + q[j];
        assert false;
    }
    assert i+1 <= i0 < j0 <= j && q[i0] + q[j0] == x;
}

lemma PreservesAddendsWhenSumBig(q: seq<int>, x: int, i: nat, j: nat)
    requires Sorted(q)
    requires 0 <= i < j < |q|
    requires q[i] + q[j] > x
    requires exists i0, j0 :: i <= i0 < j0 <= j && q[i0] + q[j0] == x
    ensures exists i0, j0 :: i <= i0 < j0 <= j-1 && q[i0] + q[j0] == x
{
    var i0, j0 :| i <= i0 < j0 <= j && q[i0] + q[j0] == x;
    if j0 == j {
        // q[i0] + q[j] == x, but q[i] + q[j] > x and i0 >= i
        // Since sorted, q[i0] >= q[i], so q[i0] + q[j] >= q[i] + q[j] > x
        // This contradicts q[i0] + q[j] == x
        assert q[i] <= q[i0];
        assert q[i] + q[j] <= q[i0] + q[j];
        assert false;
    }
    assert i <= i0 < j0 <= j-1 && q[i0] + q[j0] == x;
}
// </vc-helpers>

// <vc-spec>
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i]+q[j] == x
// </vc-spec>
// <vc-code>
{
  i := 0;
  j := |q| - 1;
  
  while i < j
    invariant 0 <= i < j < |q|
    invariant exists i0, j0 :: i <= i0 < j0 <= j && q[i0] + q[j0] == x
    decreases j - i
  {
    var sum := q[i] + q[j];
    if sum == x {
      return;
    } else if sum < x {
      PreservesAddendsWhenSumSmall(q, x, i, j);
      i := i + 1;
    } else {
      PreservesAddendsWhenSumBig(q, x, i, j);
      j := j - 1;
    }
  }
}
// </vc-code>

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
    0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
    0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
    requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
    q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
    requires AreOreredIndices(q, i, j)
{
    HasAddends(q[i..(j + 1)], x)
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
    AreOreredIndices(q, i, j) &&
    HasAddendsInIndicesRange(q, x, i, j) &&
    AreAddendsIndices(q, sum, i, j)
}

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
    requires HasAddends(q, x)
    requires Sorted(q)
    requires sum > x;
    requires LoopInv(q, x, i, j, sum)
    ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
    assert q[i..j] < q[i..(j + 1)];
}