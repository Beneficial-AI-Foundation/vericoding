// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsEven(x: int): bool { x % 2 == 0 }
function IsInTargetSet(x: int): bool { x == 2 || x == 4 || x == 6 || x == 8 }
// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)

  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
// </vc-spec>
// <vc-code>
{
  var length := (a + b) % 4 + 1;
  result := [];
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant forall j : int :: j >= 0 && j < |result| ==> IsEven(result[j]) && IsInTargetSet(result[j])
  {
    result := result + [2 + (i % 4) * 2];
    i := i + 1;
  }
}
// </vc-code>
