predicate Sorted(q: seq<int>)
{
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
    exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

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

// <vc-helpers>
lemma SliceSorted(q: seq<int>, i: nat, j: nat)
    requires Sorted(q)
    requires 0 <= i <= j < |q|
    ensures Sorted(q[i..(j + 1)])
{
    // The body is provable from the definition of Sorted(q)
}

lemma MoveI_preserves_hasadd(q: seq<int>, x: int, i: nat, j: nat, sum: int)
    requires Sorted(q)
    requires AreOreredIndices(q, i, j)
    requires HasAddendsInIndicesRange(q, x, i, j)
    requires AreAddendsIndices(q, sum, i, j)
    requires sum < x
    ensures HasAddendsInIndicesRange(q, x, i + 1, j)
{
    var s := q[i..(j + 1)];
    // extract witnesses from HasAddends(s, x)
    var a, b :| 0 <= a < b < |s| && s[a] + s[b] == x;
    // show that a != 0
    // s[a] + s[b] == x and s[b] <= s[|s|-1] since s is sorted
    SliceSorted(q, i, j);
    // s[b] == q[i + b], s[|s|-1] == q[j]
    assert q[i + b] <= q[j];
    assert s[a] + s[b] == x;
    if a == 0 {
        // then s[0] + s[b] == x contradicts s[0] + s[|s|-1] < x
        // because q[i] + q[j] == sum < x
        assert s[0] + s[|s| - 1] == q[i] + q[j];
        assert s[0] + s[b] <= s[0] + s[|s| - 1];
        assert s[0] + s[|s| - 1] < x;
        assert s[0] + s[b] < x;
        // but s[0] + s[b] == x, contradiction
        assert false;
    }
    // so a >= 1, define indices for the slice starting at i+1
    var aa := a - 1;
    var bb := b - 1;
    // verify indices are within new slice
    assert 0 <= aa < bb < |s| - 1;
    // the slice q[(i+1)..(j+1)] has elements s[1..|s|)
    var t := q[(i + 1)..(j + 1)];
    assert t[aa] + t[bb] == x;
    // conclude HasAddends on the smaller slice
    assert HasAddends(t, x);
    assert HasAddendsInIndicesRange(q, x, i + 1, j);
}

lemma MoveJ_preserves_hasadd(q: seq<int>, x: int, i: nat, j: nat, sum: int)
    requires Sorted(q)
    requires AreOreredIndices(q, i, j)
    requires HasAddendsInIndicesRange(q, x, i, j)
    requires AreAddendsIndices(q, sum, i, j)
    requires sum > x
    ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
    var s := q[i..(j + 1)];
    var a, b :| 0 <= a < b < |s| && s[a] + s[b] == x;
    // show that b != |s|-1
    SliceSorted(q, i, j);
    // s[a] == q[i+a], s[|s|-1] == q[j]
    assert q[i + a] >= q[i];
    assert s[a] + s[b] == x;
    if b == |s| - 1 {
        // then s[a] + s[|s|-1] == x contradicts s[0] + s[|s|-1] > x?
        // We know q[i] + q[j] == sum > x, but that doesn't directly contradict.
        // Instead use monotonicity: s[a] >= s[0], so s[a] + s[|s|-1] >= s[0] + s[|s|-1] = sum > x
        assert s[a] + s[|s| - 1] >= s[0] + s[|s| - 1];
        assert s[0] + s[|s| - 1] == q[i] + q[j];
        assert q[i] + q[j] > x;
        assert s[a] + s[|s| - 1] > x;
        // but s[a] + s[|s|-1] == x, contradiction
        assert false;
    }
    // so b <= |s|-2, define indices for the slice ending at j-1
    var aa := a;
    var bb := b;
    // new slice u = q[i..j] has length |s|-1 and u[aa] + u[bb] == x
    var u := q[i..j];
    assert 0 <= aa < bb < |u|;
    assert u[aa] + u[bb] == x;
    assert HasAddends(u, x);
    assert HasAddendsInIndicesRange(q, x, i, j - 1);
}
// </vc-helpers>

// <vc-spec>
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i]+q[j] == x
// </vc-spec>
// <vc-code>
{
  var ii := 0;
  var jj := |q| - 1;
  var sum := q[ii] + q[jj];
  // initial invariant
  assert AreOreredIndices(q, ii, jj);
  assert HasAddendsInIndicesRange(q, x, ii, jj);
  assert AreAddendsIndices(q, sum, ii, jj);
  while ii < jj
    invariant LoopInv(q, x, ii, jj, sum)
    decreases jj - ii
  {
    if sum == x {
      i := ii;
      j := jj;
      return;
    }
    if sum < x {
      // move left index up, preserving existence of addends in new range
      MoveI_preserves_hasadd(q, x, ii, jj, sum);
      ii := ii + 1;
      sum := q[ii] + q[jj];
    } else {
      // sum > x, move right index down
      MoveJ_preserves_hasadd(q, x, ii, jj, sum);
      jj := jj - 1;
      sum := q[ii] + q[jj];
    }
  }
  // loop exited only when ii >= jj, but precondition guarantees existence,
  // so we must have found pair before; to satisfy verifier, return current if match
  // (should not happen due to precondition)
  i := ii;
  j := jj;
}
// </vc-code>

