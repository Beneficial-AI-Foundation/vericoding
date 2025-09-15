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

// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Assigns elements to a sequence by using sequence update. */
{
  rev := s; // Initialize 'rev' with 's' to have the correct length and type
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant |rev| == |s|
    invariant forall l :: 0 <= l < k ==> rev[l] == s[|s| - 1 - l]
  {
    rev := rev[k := s[|s| - 1 - k]];
    k := k + 1;
  }
}
// </vc-code>
