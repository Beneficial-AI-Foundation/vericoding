method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
// <vc-helpers>
function isSorted(s : seq<int>) : bool
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function isStrictlySorted(s : seq<int>) : bool
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

lemma lemmaMultisetInsert(s: seq<int>, x: int, i: nat)
  requires 0 <= i <= |s|
  ensures multiset(s[..i] + [x] + s[i..]) == multiset(s) + multiset{x}
{
  calc {
    multiset(s[..i] + [x] + s[i..]);
    { }
    multiset(s[..i]) + multiset([x]) + multiset(s[i..]);
  }
  assert multiset([x]) == multiset{x};
}

method Insert(s : seq<int>, x : int) returns (res : seq<int>)
  requires isSorted(s)
  ensures isSorted(res)
  ensures multiset(res) == multiset(s) + multiset{x}
  ensures |res| == |s| + 1
{
  var i := 0;
  while i < |s| && s[i] < x
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] <= x
  {
    i := i + 1;
  }
  res := s[..i] + [x] + s[i..];
  lemma lemmaMultisetInsert(s, x, i);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var temp := [];
  var i_sort := 0;
  while i_sort < |s|
    invariant 0 <= i_sort <= |s|
    invariant multiset(s[..i_sort]) == multiset(temp)
    invariant isSorted(temp)
    invariant |temp| == i_sort
  {
    temp := Insert(temp, s[i_sort]);
    i_sort := i_sort + 1;
  }
  var sorted := temp;
  if |sorted| == 0 {
    result := [];
  } else {
    result := [sorted[0]];
    var i_unique := 1;
    while i_unique < |sorted|
      invariant 1 <= i_unique <= |sorted|
      invariant isStrictlySorted(result)
      invariant forall x :: x in result <==> x in sorted[..i_unique]
      invariant sorted[i_unique-1] == sorted[..i_unique][|sorted[..i_unique]|-1]
    {
      if sorted[i_unique] != sorted[i_unique-1] {
        assert sorted[i_unique] > sorted[i_unique-1];
        result := result + [sorted[i_unique]];
      }
      i_unique := i_unique + 1;
    }
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}