// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function ReverseFunc(s: seq<int>): seq<int>
  ensures |ReverseFunc(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> ReverseFunc(s)[k] == s[|s| - 1 - k]
  decreases |s|
{
  if |s| == 0 then
    []
  else
    ReverseFunc(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  rev := ReverseFunc(s);
}
// </vc-code>
