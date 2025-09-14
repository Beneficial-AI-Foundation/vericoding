

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
  interspersed := if |numbers| == 0 then [] else seq(2 * |numbers| - 1, i requires 0 <= i < 2 * |numbers| - 1 => if i % 2 == 0 then numbers[i / 2] else delimiter);
}
// </vc-code>

