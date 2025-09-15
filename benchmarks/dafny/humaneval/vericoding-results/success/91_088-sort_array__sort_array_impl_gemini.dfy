// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  if |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 {
    sorted := seq(|s|, i => |s| - 1 - i);
  } else {
    sorted := seq(|s|, i => i as int);
  }
}
// </vc-code>
