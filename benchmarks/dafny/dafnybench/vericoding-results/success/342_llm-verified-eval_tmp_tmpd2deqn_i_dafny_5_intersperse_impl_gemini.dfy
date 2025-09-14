// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
  } else {
      interspersed := [numbers[0]];
      var i := 1;
      while i < |numbers|
          invariant 1 <= i <= |numbers|
          invariant |interspersed| == 2 * i - 1
          invariant forall k :: 0 <= k < |interspersed| && k % 2 == 0 ==> interspersed[k] == numbers[k/2]
          invariant forall k :: 0 <= k < |interspersed| && k % 2 == 1 ==> interspersed[k] == delimiter
      {
          interspersed := interspersed + [delimiter, numbers[i]];
          i := i + 1;
      }
  }
}
// </vc-code>
