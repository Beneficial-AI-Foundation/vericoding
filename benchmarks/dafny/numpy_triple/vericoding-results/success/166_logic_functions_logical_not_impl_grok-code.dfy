// <vc-preamble>
/**
 * Computes the logical NOT of each element in the input sequence according to NumPy semantics.
 * Uses NumPy's truthiness convention: zero is falsy (NOT zero = true), 
 * all non-zero values are truthy (NOT non-zero = false).
 */
// </vc-preamble>

// <vc-helpers>
function LogicalNotHelper(x: real): bool
  ensures LogicalNotHelper(x) == (x == 0.0)
{
  x == 0.0
}

function MapLogicalNot(x: seq<real>): seq<bool>
  ensures |MapLogicalNot(x)| == |x|
  ensures forall i :: 0 <= i < |x| ==> MapLogicalNot(x)[i] == LogicalNotHelper(x[i])
{
  if x == [] then []
  else MapLogicalNot(x[..|x|-1]) + [LogicalNotHelper(x[|x|-1])]
}
// </vc-helpers>

// <vc-spec>
method LogicalNot(x: seq<real>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x[j] == 0.0)
  {
    result := result + [(x[i] == 0.0)];
  }
}
// </vc-code>
