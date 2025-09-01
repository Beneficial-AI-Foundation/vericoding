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
predicate isSorted(s : seq<int>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate isStrictlySorted(s : seq<int>)
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
  calc {
    multiset(s[..i] + [x] + s[i..]);
    { lemmaMultisetInsertAux(); }
    (multiset(s[..i]) + multiset(s[i..])) + multiset{x};
    ==
    multiset(s) + multiset{x};
  }
  static lemma lemmaMultisetInsertAux() ensures multiset(s[..i]) + multiset([x]) + multiset(s[i..]) == (multiset(s[..i]) + multiset(s[i..])) + multiset{x}
  {
  }
  static lemma lemmaMultisetAppend(s1: seq<int>, s2: seq<int>) ensures multiset(s1) + multiset(s2) == multiset(s1 + s2)
  {
    calc {
      multiset(s1 + s2);
      ==
      multiset(s1) + multiset(s2);
    }
  }
  // Prove the additional calc
  calc {
    multiset(s[..i]) + multiset([x]) + multiset(s[i..]);
    ==
    multiset(s[..i] + [x] + s[i..]);
  }
  calc {
    multiset(s);
    ==
    multiset(s[..i] + s[i..]);
  }
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
    invariant forall k :: i <= k < |s| ==> x <= s[k]
  {
    i := i + 1;
  }
  res := s[..i] + [x] + s[i..];
  lemmaMultisetInsert(s, x, i);
  lemma lemmaSeqLenInsert(s: seq<int>, x: int, i: nat)
    requires 0 <= i <= |s|
    ensures |s[..i] + [x] + s[i..]| == |s| + 1
  {
    calc {
      |s[..i] + [x] + s[i..]|;
      ==
      |s[..i]| + 1 + |s[i..]|;
      ==
      i + 1 + (|s| - i);
      ==
      |s| + 1;
    }
  }
  lemmaSeqLenInsert(s, x, i);
}
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
      invariant forall x :: x in result <==> x in sorted[..i_unique] && forall x :: x in sorted[..i_unique] ==> x in s
      invariant sorted[i_unique-1] == sorted[..i_unique][|sorted[..i_unique]|-1]
      invariant |result| >= 1
      invariant result[0] == sorted[0]
      invariant forall i :: 0 <= i < |result|-1 ==> result[i] != result[i+1]
    {
      if sorted[i_unique] != sorted[i_unique-1] {
        assert sorted[i_unique] > sorted[i_unique-1];
        result := result + [sorted[i_unique]];
      }
      i_unique := i_unique + 1;
    }
  }
  assert forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j];
  assert forall x :: x in result ==> x in s;
  assert forall x :: x in s ==> x in result;
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