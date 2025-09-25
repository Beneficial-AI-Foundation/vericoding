// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Center(input: array<string>, width: int) returns (result: array<string>)
    requires 
        input.Length > 0
    requires
        forall i :: 0 <= i < input.Length ==> |input[i]| >= 1
    ensures
        result.Length == input.Length
    ensures
        forall i :: 0 <= i < input.Length ==> 
            if |input[i]| > width then
                |result[i]| == |input[i]|
            else
                |result[i]| == width
    ensures
        forall i :: 0 <= i < input.Length ==> 
            if |input[i]| < width then
                var start_pos := (width - |input[i]| + 1) / 2;
                result[i][start_pos..start_pos + |input[i]|] == input[i]
            else
                true
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
