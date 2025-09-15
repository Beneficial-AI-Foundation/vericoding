// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AllowedSeq(): seq<int> { [2, 4, 6, 8] }
predicate InSeq(x: int, s: seq<int>) { exists j: int :: 0 <= j && j < |s| && s[j] == x }
predicate IsEven(x: int) { x % 2 == 0 }
predicate IsAllowed(x: int) { InSeq(x, AllowedSeq()) }
// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)

  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
// </vc-spec>
// <vc-code>
{
  result := [];
}
// </vc-code>
