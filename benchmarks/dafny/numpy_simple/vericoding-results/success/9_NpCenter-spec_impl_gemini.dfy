// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed type mismatch in string concatenation. */
function Spaces(n: nat): string
    ensures |Spaces(n)| == n
    ensures forall i :: 0 <= i < n ==> Spaces(n)[i] == ' '
{
    if n == 0 then ""
    else " " + Spaces(n-1)
}
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
    /* code modified by LLM (iteration 2): The previous failure was a compilation error in a helper function; the main logic is correct. */
    result := new string[input.Length];
    var i := 0;
    while i < input.Length
        invariant 0 <= i <= input.Length
        invariant result.Length == input.Length
        invariant forall j :: 0 <= j < i ==> 
            if |input[j]| > width then
                |result[j]| == |input[j]|
            else
                |result[j]| == width
        invariant forall j :: 0 <= j < i ==> 
            if |input[j]| < width then
                var start_pos_j := (width - |input[j]| + 1) / 2;
                result[j][start_pos_j .. start_pos_j + |input[j]|] == input[j]
            else
                true
    {
        var s := input[i];
        var len := |s|;

        if len >= width {
            result[i] := s;
        } else {
            var start_pos := (width - len + 1) / 2;
            var right_pad_len := width - len - start_pos;
            assert start_pos >= 0;
            assert right_pad_len >= 0;
            result[i] := Spaces(start_pos) + s + Spaces(right_pad_len);
        }

        i := i + 1;
    }
}
// </vc-code>
