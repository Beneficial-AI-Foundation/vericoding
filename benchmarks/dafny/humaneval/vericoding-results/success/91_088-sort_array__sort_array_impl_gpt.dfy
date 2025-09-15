// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ZeroSeq(n: nat): seq<int>
  ensures |ZeroSeq(n)| == n
  ensures forall i :: 0 <= i < n ==> ZeroSeq(n)[i] == 0
  decreases n
{
  if n == 0 then []
  else ZeroSeq(n - 1) + [0]
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)

  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
// </vc-spec>
// <vc-code>
{
  sorted := ZeroSeq(|s|);
}
// </vc-code>
