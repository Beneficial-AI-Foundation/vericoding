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
function isSorted(s : seq<int>) : bool
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function isStrictlySorted(s : seq<int>) : bool
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] < s[j]
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
}

method SortSeq(s : seq<int>) returns (sorted : seq<int>)
  ensures isSorted(sorted)
  ensures |s| == |sorted|
  ensures multiset(s) == multiset(sorted)
{
  var temp := [];
  var i := 0;
  while i < |s|
    invariant multiset(s[..i]) == multiset(temp)
    invariant isSorted(temp)
    invariant |temp| == i
  {
    temp := Insert(temp, s[i]);
    i := i + 1;
  }
  sorted := temp;
}

method uniqueSorted(s : seq<int>) returns (result : seq<int>)
  requires isSorted(s)
  ensures isStrictlySorted(result)
  ensures forall x :: x in s <==> x in result
{
  if |s| == 0 {
    result := [];
  } else {
    var temp := [s[0]];
    var i := 1;
    while i < |s|
      invariant 1 <= i <= |s|
      invariant isStrictlySorted(temp)
      invariant forall x :: x in temp <==> x in s[..i]
      invariant s[i-1] == s[..i][|s[..i]|-1]
    {
      if s[i] != s[i-1] {
        temp := temp + [s[i]];
      }
      i := i + 1;
    }
    result := temp;
  }
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
{
  var sorted := SortSeq(s);
  result := uniqueSorted(sorted);
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