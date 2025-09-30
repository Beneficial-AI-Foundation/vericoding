// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Subtract(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Vectors must have the same length
  requires |x1| == |x2|
  
  // Result has the same length as input vectors
  ensures |result| == |x1|
  
  // Main postcondition: element-wise subtraction
  ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] - x2[i]
  
  // Mathematical property: subtracting zero preserves the original value
  ensures forall i :: 0 <= i < |result| ==> (x2[i] == 0.0 ==> result[i] == x1[i])
  
  // Mathematical property: subtracting a value from itself yields zero
  ensures forall i :: 0 <= i < |result| ==> (x1[i] == x2[i] ==> result[i] == 0.0)
  
  // Mathematical property: anti-commutativity
  ensures forall i :: 0 <= i < |result| ==> result[i] == -(x2[i] - x1[i])
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x1[j] - x2[j]
  {
    result := result + [x1[i] - x2[i]];
    i := i + 1;
  }
}
// </vc-code>
