method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ReverseLemma(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures |s| - 1 - k >= 0
  ensures |s| - 1 - k < |s|
{
}

lemma ReversePreservesLength(s: seq<int>, rev: seq<int>)
  requires |rev| == |s|
  ensures |rev| == |s|
{
}

lemma ReverseIndexLemma(s: seq<int>, rev: seq<int>, i: int)
  requires 0 <= |rev| <= |s|
  requires forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - i - 1 + k]
  requires -1 <= i < |s|
  ensures |rev| == |s| - i - 1
  ensures forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - |rev| + k]
{
  if |rev| > 0 {
    var m := |rev|;
    forall k | 0 <= k < m
      ensures rev[k] == s[|s| - m + k] 
    {
      assert rev[k] == s[|s| - i - 1 + k];
      calc {
        |s| - i - 1;
        == { assert m == |s| - i - 1; }
        m;
      }
      assert |s| - i - 1 + k == |s| - m + k;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  rev := [];
  var i := |s| - 1;
  while i >= 0
    invariant -1 <= i < |s|
    invariant |rev| == |s| - i - 1
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - i - 1 + k]
  {
    rev := [s[i]] + rev;
    i := i - 1;
    
    if i >= 0 {
      forall k | 0 <= k < |rev|
        ensures rev[k] == s[|s| - i - 1 + k]
      {
        if k == 0 {
          assert rev[0] == s[i + 1];
          assert |s| - i - 1 + 0 == |s| - (i + 1);
        } else {
          assert rev[k] == s[|s| - (i + 1) - 1 + (k - 1)];
          assert |s| - (i + 1) - 1 + (k - 1) == |s| - i - 2 + k - 1;
          assert |s| - i - 1 + k == |s| - i - 2 + k - 1 + 2;
        }
      }
    }
  }
}
// </vc-code>

function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// pure-end