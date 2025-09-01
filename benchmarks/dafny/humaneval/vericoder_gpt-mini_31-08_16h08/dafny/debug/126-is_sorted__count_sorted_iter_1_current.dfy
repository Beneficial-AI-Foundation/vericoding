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
    // For any k < pos, k <= pos-1, so a[k] <= a[pos-1] < x, hence a[k] != x.
    var k := 0;
    while k < pos
      invariant 0 <= k <= pos
      decreases pos - k
    {
      assert k <= pos - 1;
      assert a[k] <= a[pos - 1]; // from sortedness with 0 <= k <= pos-1 < |a|
      assert a[pos - 1] < x;     // from precondition
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
  // From pos < i and a[pos] == x and sortedness we have a[pos] <= a[i].
  // Since a[i] != x and a[i] >= a[pos] == x, we get a[i] > x.
  assert a[pos] <= a[i];
  assert a[i] >= x;
  assert a[i] > x;

  var k := i;
  while k < |a|
    invariant i <= k <= |a|
    decreases |a| - k
  {
    // a[i] <= a[k] by sortedness, so a[k] > x.
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
  // Show the two sets are equal by mutual containment.
  // First: if 0 <= k < |a| && a[k] == x then pos <= k < i.
  // If k < pos impossible by precondition; if k >= i impossible by precondition.
  // Second: if pos <= k < i and a[k] == x then obviously 0 <= k < |a| && a[k] == x.
  //
  // We prove extensionality of the two sets via a trivial forall proof.
  // (Dafny will use these facts to conclude equality of cardinalities.)
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
          // contradicts precondition that no occurrence before pos
          assert false;
        }
        if k >= i {
          // contradicts precondition that no occurrence at or after i
          assert false;
        }
        // Hence pos <= k < i and a[k] == x
      } else {
        // If pos <= k < i then by precondition a[k] == x, contradiction.
        if pos <= k && k < i {
          assert false;
        }
      }
      k := k + 1;
    }
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
  // invariants:
  // 0 <= pos <= i <= |a|
  // all elements in [pos, i) equal x
  // count equals number of indices in [pos, i) with a[k]==x
  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant forall k :: pos <= k < i ==> a[k] == x
    invariant count == |set k | pos <= k < i && a[k] == x|
  {
    count := count + 1;
    i := i + 1;
  }

  // prove there are no occurrences before pos
  NoOccBefore(a, x, pos);

  // prove there are no occurrences at or after i
  if i < |a| {
    if pos < i {
      // we have some equalities in [pos, i), so use NoOccAfter
      NoOccAfter(a, x, pos, i);
    } else {
      // pos == i cannot happen here because a[pos] == x (precondition),
      // so the loop would have executed at least once; therefore this branch is unreachable.
      assert pos != i;
    }
  }

  // Now the set of indices where a[k]==x is exactly pos <= k < i.
  CountSetFromPos(a, x, pos, i);

  // Using the loop invariant count == |set k | pos <= k < i && a[k] == x|
  // and CountSetFromPos, conclude count == count_set(a, x).
  assert count == |set k | 0 <= k < |a| && a[k] == x|;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end