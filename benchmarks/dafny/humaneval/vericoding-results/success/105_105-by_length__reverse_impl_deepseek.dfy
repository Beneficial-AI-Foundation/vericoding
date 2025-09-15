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

function ReverseAux(s: seq<int>, i: int): seq<int>
  requires 0 <= i <= |s|
  ensures |ReverseAux(s, i)| == i
  ensures forall k :: 0 <= k < i ==> ReverseAux(s, i)[k] == s[i - 1 - k]
{
  if i == 0 then []
  else [s[i - 1]] + ReverseAux(s, i - 1)
}

// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  rev := ReverseAux(s, |s|);
}
// </vc-code>
