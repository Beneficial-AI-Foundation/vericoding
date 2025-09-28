// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Maximum(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Arrays must have the same length
  requires |x1| == |x2|
  // Result has the same length as input arrays
  ensures |result| == |x1|
  // Each element is the maximum of corresponding elements from x1 and x2
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == if x1[i] >= x2[i] then x1[i] else x2[i]
  // Each result element is greater than or equal to both input elements
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] >= x1[i] && result[i] >= x2[i]
  // Each result element equals one of the corresponding input elements
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == x1[i] || result[i] == x2[i]
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == if x1[j] >= x2[j] then x1[j] else x2[j]
    invariant forall j :: 0 <= j < i ==> result[j] >= x1[j] && result[j] >= x2[j]
    invariant forall j :: 0 <= j < i ==> result[j] == x1[j] || result[j] == x2[j]
  {
    if x1[i] >= x2[i] {
      result := result + [x1[i]];
    } else {
      result := result + [x2[i]];
    }
  }
}
// </vc-code>
