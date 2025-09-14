method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function MinIndex(s: seq<int>): nat
  requires |s| > 0
  decreases |s|
  ensures 0 <= MinIndex(s) < |s|
  ensures forall i :: 0 <= i < |s| ==> s[MinIndex(s)] <= s[i]
{
  if |s| == 1 then 0 else
    var j := MinIndex(s[1..]);
    if s[0] <= s[1 + j] then 0 else 1 + j
}

function RemoveAt(s: seq<int>, k: nat): seq<int>
  requires 0 <= k < |s|
  ensures |RemoveAt(s,k)| == |s| - 1
  ensures forall i :: 0 <= i < k ==> RemoveAt(s,k)[i] == s[i]
  ensures forall i :: k <= i < |RemoveAt(s,k)| ==> RemoveAt(s,k)[i] == s[i+1]
  ensures multiset(s) == multiset([s[k]] + RemoveAt(s,k))
{
  s[..k] + s[k+1..]
}

function SortSeqImpl(s: seq<int>): seq<int>
  decreases |s|
  ensures forall i, j :: 0 <= i < j < |SortSeqImpl(s)| ==> SortSeqImpl(s)[i] <= SortSeqImpl(s)[j]
  ensures |SortSeqImpl(s)| == |s|
  ensures multiset(s) == multiset(SortSeqImpl(s))
{
  if |s| <= 1 then s
  else
    var k := MinIndex(s);
    [s[k]] + SortSeqImpl(RemoveAt(s,k))
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := SortSeqImpl(s);
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
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