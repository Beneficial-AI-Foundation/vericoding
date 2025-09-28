// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed syntax error in function signature */
function select(condition: bool, x: real, y: real): real
{
  if condition then x else y
}

/* helper modified by LLM (iteration 3): fixed function signature to be valid Dafny syntax */
function safe_access<T>(s: seq<T>, index: int): T
  requires 0 <= index < |s|
{
  s[index]
}
// </vc-helpers>

// <vc-spec>
method NumpyWhere(condition: seq<bool>, x: seq<real>, y: seq<real>) returns (result: seq<real>)
  // All input sequences must have the same length
  requires |condition| == |x| == |y|
  
  // The result sequence has the same length as the input sequences
  ensures |result| == |condition|
  
  // For each index i, if condition[i] is true, result[i] equals x[i], 
  // otherwise result[i] equals y[i]
  ensures forall i :: 0 <= i < |result| ==> 
    if condition[i] then result[i] == x[i] else result[i] == y[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed compilation error and simplified implementation */
  result := [];
  var i := 0;
  while i < |condition|
    invariant 0 <= i <= |condition|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> if condition[j] then result[j] == x[j] else result[j] == y[j]
  {
    result := result + [if condition[i] then x[i] else y[i]];
    i := i + 1;
  }
}
// </vc-code>
