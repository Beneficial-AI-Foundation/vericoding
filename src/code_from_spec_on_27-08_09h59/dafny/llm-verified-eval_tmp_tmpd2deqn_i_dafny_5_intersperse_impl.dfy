// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if |numbers| == 0 {
    interspersed := [];
  } else {
    interspersed := [numbers[0]];
    var i := 1;
    while i < |numbers|
      invariant 1 <= i <= |numbers|
      invariant |interspersed| == 2 * i - 1
      invariant forall j :: 0 <= j < |interspersed| ==> j % 2 == 0 ==> interspersed[j] == numbers[j / 2]
      invariant forall j :: 0 <= j < |interspersed| ==> j % 2 == 1 ==> interspersed[j] == delimiter
    {
      interspersed := interspersed + [delimiter, numbers[i]];
      i := i + 1;
    }
  }
}
// </vc-code>
