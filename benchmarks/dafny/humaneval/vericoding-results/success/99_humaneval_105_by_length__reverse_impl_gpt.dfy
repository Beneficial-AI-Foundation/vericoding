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
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' to satisfy parser and provide a generic reverse prefix helper */
function ReversePrefix<A>(s: seq<A>, i: nat): seq<A>
  requires i <= |s|
  decreases i
{
  if i == 0 then [] else [s[i - 1]] + ReversePrefix(s, i - 1)
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative reverse with loop invariants */
  var i := 0;
  rev := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[i - 1 - k]
    decreases |s| - i
  {
    rev := [s[i]] + rev;
    i := i + 1;
  }
}
// </vc-code>
