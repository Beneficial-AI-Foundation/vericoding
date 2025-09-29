// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var lower := if a <= b then a else b;
  var upper := if a <= b then b else a;
  result := [];
  
  if lower <= 2 && 2 <= upper {
    result := result + [2];
  }
  if lower <= 4 && 4 <= upper {
    result := result + [4];
  }
  if lower <= 6 && 6 <= upper {
    result := result + [6];
  }
  if lower <= 8 && 8 <= upper {
    result := result + [8];
  }
}
// </vc-code>
