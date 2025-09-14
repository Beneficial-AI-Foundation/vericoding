predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
function InsertElem(x: int, s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + InsertElem(x, s[1..])
}

function InsertSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else InsertElem(s[0], InsertSeq(s[1..]))
}

predicate SortedSeq(s: seq<int>)
{
  forall l, k :: 0 <= l <= k < |s| ==> s[l] <= s[k]
}

lemma {:auto} InsertElem_preserves_sorted(x:int, s: seq<int>)
  requires SortedSeq(s)
  ensures SortedSeq(InsertElem(x,s))
  decreases |s|
{
  if |s| == 0 {
  } else if x <= s[0] {
  } else {
    InsertElem_preserves_sorted(x, s[1..]);
  }
}

lemma InsertElem_length(x:int, s: seq<int>)
  ensures |InsertElem(x,s)| == |s| + 1
  decreases |s|
{
  if |s| == 0 {
  } else {
    InsertElem_length(x, s[1..]);
  }
}

lemma InsertSeq_length(s: seq<int>)
  ensures |InsertSeq(s)| == |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    InsertSeq_length(s[1..]);
    InsertElem_length(s[0], InsertSeq(s[1..]));
  }
}

lemma InsertElem_preserves_multiset(x:int, s: seq<int>)
  ensures multiset(InsertElem(x,s)) == multiset(s) + multiset([x])
  decreases |s|
{
  if |s| == 0 {
    assert InsertElem(x,s) == [x];
    assert multiset(InsertElem(x,s)) == multiset([x]);
    assert multiset(s) + multiset([x]) == multiset([]) + multiset([x]);
  } else if x <= s[0] {
    assert InsertElem(x,s) == [x] + s;
    assert multiset(InsertElem(x,s)) == multiset([x] + s);
    assert multiset([x] + s) == multiset([x]) + multiset(s);
    // commutativity of multiset addition holds
    assert multiset([x]) + multiset(s) == multiset(s) + multiset([x]);
  } else {
    // InsertElem(x,s) == [s[0]] + InsertElem(x,s[1..])
    assert InsertElem(x,s) == [s[0]] + InsertElem(x,s[1..]);
    assert multiset(InsertElem(x,s)) == multiset([s[0]]) + multiset(InsertElem(x,s[1..]));
    InsertElem_preserves_multiset(x, s[1..]);
    assert multiset(InsertElem(x,s)) == multiset([s[0]]) + (multiset(s[1..]) + multiset([x]));
    assert multiset([s[0]]) + (multiset(s[1..]) + multiset([x])) == (multiset([s[0]]) + multiset(s[1..])) + multiset([x]);
    assert (multiset([s[0]]) + multiset(s[1..])) + multiset([x]) == multiset(s) + multiset([x]);
  }
}

lemma InsertSeq_preserves_sorted(s: seq<int>)
  ensures SortedSeq(InsertSeq(s))
  decreases |s|
{
  if |s| == 0 {
  } else {
    InsertSeq_preserves_sorted(s[1..]);
    InsertElem_preserves_sorted(s[0], InsertSeq(s[1..]));
  }
}

lemma InsertSeq_preserves_multiset(s: seq<int>)
  ensures multiset(InsertSeq(s)) == multiset(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    InsertSeq_preserves_multiset(s[1..]);
    // multiset(InsertSeq(s)) == multiset(InsertElem(s[0], InsertSeq(s[1..])))
    assert InsertSeq(s) == InsertElem(s[0], InsertSeq(s[1..]));
    InsertElem_preserves_multiset(s[0], InsertSeq(s[1..]));
    assert multiset(InsertSeq(s)) == multiset(InsertSeq(s[1..])) + multiset([s[0]]);
    assert multiset(InsertSeq(s)) == multiset(s[1..]) + multiset([s[0]]);
    assert multiset(s[1..]) + multiset([s[0]]) == multiset(s);
  }
}
// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var s := a[..]; // snapshot of original array
  var t := InsertSeq(s);
  // establish length of t
  InsertSeq_length(s);
  assert |t| == |s|;
  assert |s| == n;
  // copy t back into a
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> a[k] == t[k]
    invariant forall k :: i <= k < n ==> a[k] == s[k]
  {
    a[i] := t[i];
    i := i + 1;
  }
  // now a[..] == t
  assert a[..] == t;
  // prove postconditions using lemmas
  InsertSeq_preserves_sorted(s);
  assert SortedSeq(t);
  assert SortedSeq(a[..]);
  // convert SortedSeq(a[..]) to sorted_seg(a,0,n-1)
  assert forall l, k :: 0 <= l <= k <= n-1 ==> a[l] <= a[k];
  InsertSeq_preserves_multiset(s);
  assert multiset(a[..]) == multiset(t);
  assert multiset(t) == multiset(s);
  assert multiset(a[..]) == multiset(s);
}
// </vc-code>

