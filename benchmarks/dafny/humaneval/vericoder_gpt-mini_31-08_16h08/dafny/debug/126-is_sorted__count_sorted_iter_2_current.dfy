method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma NoOccBefore(a: seq<int>, x: int, pos: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  ensures forall k :: 0 <= k < pos ==> a[k] != x
{
  if pos == 0 {
    // nothing to prove
  } else {
    var k := 0;
    while k < pos
      invariant 0 <= k <= pos
      decreases pos - k
    {
      assert k <= pos - 1;
      assert a[k] <= a[pos - 1];
      assert a[pos - 1] < x;
      assert a[k] < x;
      assert a[k] != x;
      k := k + 1;
    }
  }
}

lemma NoOccAfter(a: seq<int>, x: int, pos: int, i: int)
  requires forall p, q :: 0 <= p <= q < |a| ==> a[p] <= a[q]
  requires 0 <= pos < i < |a|
  requires a[pos] == x
  requires forall k :: pos <= k < i ==> a[k] == x
  requires a[i] != x
  ensures forall k :: i <= k < |a| ==> a[k] != x
{
  assert a[pos] <= a[i];
  assert a[i] >= x;
  assert a[i] > x;

  var k := i;
  while k < |a|
    invariant i <= k <= |a|
    decreases |a| - k
  {
    assert a[i] <= a[k];
    assert a[k] > x;
    assert a[k] != x;
    k := k + 1;
  }
}

lemma CountSetFromPos(a: seq<int>, x: int, pos: int, i: int)
  requires forall p, q :: 0 <= p <= q < |a| ==> a[p] <= a[q]
  requires 0 <= pos <= i <= |a|
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires forall k :: pos <= k < i ==> a[k] == x
  requires forall k :: 0 <= k < pos ==> a[k] != x
  requires forall k :: i <= k < |a| ==> a[k] != x
  ensures |set k | 0 <= k < |a| && a[k] == x| == |set k | pos <= k < i && a[k] == x|
{
  assert forall k :: 0 <= k < |a| ==>
                      (a[k] == x) <==>
                      (pos <= k < i && a[k] == x)
  by {
    var k := 0;
    while k < |a|
      invariant 0 <= k <= |a|
      decreases |a| - k
    {
      if a[k] == x {
        if k < pos {
          assert false;
        }
        if k >= i {
          assert false;
        }
      } else {
        if pos <= k && k < i {
          assert false;
        }
      }
      k := k + 1;
    }
  }
}

lemma RangeAllEqCard(a: seq<int>, x: int, pos: int, i: int)
  requires 0 <= pos <= i <= |a|
  requires forall k :: pos <= k < i ==> a[k] == x
  ensures |set k | pos <= k < i && a[k] == x| == i - pos
{
  if pos == i {
    // empty range, cardinality 0
  } else {
    // We prove by relating the set for i to that for i-1.
    // Show extensionality: for all k in 0..|a|-1,
    // (pos <= k < i && a[k]==x) <==> ((pos <= k < i-1 && a[k]==x) || k == i-1 && a[k]==x)
    assert forall k :: 0 <= k < |a| ==>
      (pos <= k < i && a[k] == x) <==>
      ((pos <= k < i-1 && a[k] == x) || (k == i-1 && a[k] == x))
    by {
      var k := 0;
      while k < |a|
        invariant 0 <= k <= |a|
        decreases |a| - k
      {
        if pos <= k < i && a[k] == x {
          if k < i-1 {
            // then pos <= k < i-1 && a[k]==x holds
          } else {
            // k >= i-1, but k < i so k == i-1
            assert k == i-1;
            assert k == i-1 && a[k] == x;
          }
        } else {
          if (pos <= k < i-1 && a[k] == x) || (k == i-1 && a[k] == x) {
            // if k == i-1 and a[k]==x then pos <= k < i and a[k]==x would hold, contradiction
            assert false;
          }
        }
        k := k + 1;
      }
    }

    // From extensionality we get the cardinalities differ by exactly 1.
    RangeAllEqCard(a, x, pos, i - 1);
    assert |set k | pos <= k < i && a[k] == x| == |set k | pos <= k < i-1 && a[k] == x| + 1;
    // Combine with induction hypothesis to conclude the result.
  }
}
// </vc-helpers>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  // pre-conditions-start
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  // pre-conditions-end
  // post-conditions-start
  ensures count == count_set(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := pos;
  count := 0;
  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant forall k :: pos <= k < i ==> a[k] == x
    invariant count == i - pos
  {
    count := count + 1;
    i := i + 1;
  }

  NoOccBefore(a, x, pos);

  if i < |a| {
    if pos < i {
      NoOccAfter(a, x, pos, i);
    } else {
      assert pos != i;
    }
  }

  CountSetFromPos(a, x, pos, i);
  RangeAllEqCard(a, x, pos, i);

  assert count == i - pos;
  assert |set k | pos <= k < i && a[k] == x| == i - pos;
  assert count == |set k | pos <= k < i && a[k] == x|;
  assert count == |set k | 0 <= k < |a| && a[k] == x|;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end