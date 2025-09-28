// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function inInterval(x:int, a:int, b:int): bool {
  (x >= a && x <= b) || (x >= b && x <= a)
}
// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> result[i] in {2, 4, 6, 8}
  ensures forall i :: 0 <= i < |result| - 1 ==> result[i] < result[i + 1]
  ensures forall x :: x in result ==> (x >= a && x <= b) || (x >= b && x <= a)
  ensures forall x :: x in {2, 4, 6, 8} && ((x >= a && x <= b) || (x >= b && x <= a)) ==> x in result
// </vc-spec>
// <vc-code>
{
  var s: seq<int> := [];
  if inInterval(2, a, b) {
    s := s + [2];
  }
  if inInterval(4, a, b) {
    s := s + [4];
  }
  if inInterval(6, a, b) {
    s := s + [6];
  }
  if inInterval(8, a, b) {
    s := s + [8];
  }
  result := s;
}
// </vc-code>
