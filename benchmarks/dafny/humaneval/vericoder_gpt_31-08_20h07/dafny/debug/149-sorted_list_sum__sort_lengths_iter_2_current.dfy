function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate SortedByLen(s: seq<string>)
{
  forall x:int, y:int :: 0 <= x < y < |s| ==> |s[x]| <= |s[y]|
}

predicate EvenAll(s: seq<string>)
{
  forall i:int :: 0 <= i < |s| ==> |s[i]| % 2 == 0
}

method InsertByLen(acc: seq<string>, x: string) returns (res: seq<string>)
  requires SortedByLen(acc)
  requires EvenAll(acc)
  requires |x| % 2 == 0
  ensures SortedByLen(res)
  ensures |res| == |acc| + 1
  ensures multiset(res) == multiset(acc) + multiset([x])
  ensures EvenAll(res)
{
  var i := 0;
  while i < |acc| && |acc[i]| < |x|
    invariant 0 <= i <= |acc|
    invariant SortedByLen(acc)
    invariant forall k:int :: 0 <= k < i ==> |acc[k]| < |x|
    decreases |acc| - i
  {
    i := i + 1;
  }

  // Construct result by inserting at position i
  res := acc[..i] + [x] + acc[i..];

  // Basic facts about slices and concatenation
  assert |acc[..i]| == i;
  assert |res| == |acc[..i]| + 1 + |acc[i..]|;

  // Show elements after i in acc are >= |x|
  if i < |acc| {
    assert |x| <= |acc[i]|;
    assert forall k:int :: i <= k < |acc| ==> |acc[i]| <= |acc[k]|
      by {
        // From SortedByLen(acc)
      }
    assert forall k:int :: i <= k < |acc| ==> |x| <= |acc[k]|;
  } else {
    assert i == |acc|;
  }

  // Prove SortedByLen(res) by case analysis on indices
  assert forall p:int, q:int
           :: 0 <= p < q < |res|
           ==> |res[p]| <= |res[q]|
    by {
      // Map indices in res back to acc or x
      if p < i && q < i {
        // both from left part acc[..i]
        assert res[p] == acc[p];
        assert res[q] == acc[q];
        assert |acc[p]| <= |acc[q]|; // SortedByLen(acc)
      } else if p < i && q == i {
        // left part and x
        assert res[p] == acc[p];
        assert res[q] == x;
        assert |acc[p]| < |x|; // from loop invariant
        assert |acc[p]| <= |x|;
      } else if p < i && q > i {
        // left part and right part
        assert res[p] == acc[p];
        assert res[q] == acc[q-1];
        // From loop invariant and construction, |acc[p]| < |x| <= |acc[q-1]|
        if i < |acc| {
          assert |x| <= |acc[q-1]|;
          assert |acc[p]| < |x|;
          assert |acc[p]| <= |acc[q-1]|;
        } else {
          // i == |acc|, so q cannot be > i because |res| = |acc| + 1
          // but Dafny requires a consequence; this branch is unreachable
        }
      } else if p == i && q > i {
        // x and right part
        assert res[p] == x;
        assert res[q] == acc[q-1];
        if i < |acc| {
          assert |x| <= |acc[q-1]|;
        } else {
          // i == |acc|; then right part is empty, so this branch unreachable
        }
      } else if p == i && q == i {
        // impossible since p < q
      } else if p > i && q > i {
        // both from right part acc[i..]
        assert res[p] == acc[p-1];
        assert res[q] == acc[q-1];
        assert |acc[p-1]| <= |acc[q-1]|; // SortedByLen(acc)
      } else if p > i && q == i {
        // impossible since p < q
      } else {
        // p >= i and q < i cannot happen due to p < q
      }
    };

  // Prove EvenAll(res)
  assert forall j:int :: 0 <= j < |res| ==> |res[j]| % 2 == 0
    by {
      if j < i {
        assert res[j] == acc[j];
        assert |acc[j]| % 2 == 0; // EvenAll(acc)
      } else if j == i {
        assert res[j] == x;
        assert |x| % 2 == 0;
      } else {
        assert res[j] == acc[j-1];
        assert |acc[j-1]| % 2 == 0; // EvenAll(acc)
      }
    };

  // Prove multiset(res) == multiset(acc) + multiset([x])
  // Use algebra of multisets over concatenation
  assert multiset(res) == multiset(acc[..i] + [x]) + multiset(acc[i..]);
  assert multiset(acc[..i] + [x]) == multiset(acc[..i]) + multiset([x]);
  assert acc[..i] + acc[i..] == acc;
  assert multiset(acc[..i]) + multiset(acc[i..]) == multiset(acc);
  assert (multiset(acc[..i]) + multiset([x])) + multiset(acc[i..]) == multiset(acc) + multiset([x]);
}
// </vc-helpers>

// <vc-spec>
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
// </vc-spec>
// <vc-code>
{
  var acc: seq<string> := [];
  var rest: seq<string> := list;

  // Establish invariants initially
  assert SortedByLen(acc);
  assert EvenAll(acc);
  assert EvenAll(rest);
  assert multiset(acc) + multiset(rest) == multiset(list);
  assert |acc| + |rest| == |list|;

  while |rest| > 0
    invariant SortedByLen(acc)
    invariant EvenAll(acc)
    invariant EvenAll(rest)
    invariant multiset(acc) + multiset(rest) == multiset(list)
    invariant |acc| + |rest| == |list|
    decreases |rest|
  {
    ghost var oldRest := rest;
    var x := rest[0];
    rest := rest[1..];

    // Maintain EvenAll(rest) from EvenAll(oldRest)
    assert forall i:int :: 0 <= i < |rest| ==> |rest[i]| % 2 == 0;

    // Insert x into acc preserving sortedness and other invariants
    acc := InsertByLen(acc, x);

    // Update multiset invariant
    assert multiset(oldRest) == multiset([x]) + multiset(rest);
    assert multiset(acc) + multiset(rest) == (multiset(acc) - multiset([x])) + multiset([x]) + multiset(rest) || true;
    assert multiset(acc) + multiset(rest) == (multiset(acc) + multiset(rest));
    assert multiset(acc) + multiset(rest) == multiset(list);

    // Update length invariant
    assert |acc| + |rest| == |list|;
  }

  sorted := acc;

  // Postconditions follow from invariants
}
// </vc-code>

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}