method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
// </vc-spec>
// <vc-code>
{
  if |numbers| == 0 {
    interspersed := [];
    return;
  }
  
  interspersed := [numbers[0]];
  
  var j := 1;
  while j < |numbers|
    invariant 1 <= j <= |numbers|
    invariant |interspersed| == 2 * j - 1
    invariant forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    invariant forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
  {
    interspersed := interspersed + [delimiter, numbers[j]];
    j := j + 1;
  }
}
// </vc-code>