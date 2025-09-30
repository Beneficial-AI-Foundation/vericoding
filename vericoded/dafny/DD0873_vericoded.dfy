

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
        interspersed := [];
        var i := 0;
        while i < |numbers| - 1
            invariant 0 <= i <= |numbers| - 1
            invariant |interspersed| == 2 * i
            invariant forall j :: 0 <= j < |interspersed| ==> j % 2 == 0 ==> 
                        interspersed[j] == numbers[j / 2]
            invariant forall j :: 0 <= j < |interspersed| ==> j % 2 == 1 ==>
                        interspersed[j] == delimiter
        {
            interspersed := interspersed + [numbers[i], delimiter];
            i := i + 1;
        }
        interspersed := interspersed + [numbers[|numbers| - 1]];
    }
}
// </vc-code>

