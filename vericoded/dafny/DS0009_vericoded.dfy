// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function PadString(s: string, width: int): string
    requires |s| >= 1
    requires |s| <= width
    ensures |PadString(s, width)| == width
    ensures var start_pos := (width - |s| + 1) / 2;
            PadString(s, width)[start_pos..start_pos + |s|] == s
{
    var total_padding := width - |s|;
    var left_padding := (total_padding + 1) / 2;
    var right_padding := total_padding - left_padding;
    seq(left_padding, _ => ' ') + s + seq(right_padding, _ => ' ')
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
    result := new string[input.Length];
    var i := 0;
    while i < input.Length
        invariant 0 <= i <= input.Length
        invariant forall j :: 0 <= j < i ==>
            if |input[j]| > width then
                |result[j]| == |input[j]|
            else
                |result[j]| == width
        invariant forall j :: 0 <= j < i ==>
            if |input[j]| < width then
                var start_pos := (width - |input[j]| + 1) / 2;
                result[j][start_pos..start_pos + |input[j]|] == input[j]
            else
                true
    {
        if |input[i]| > width {
            result[i] := input[i];
        } else if |input[i]| == width {
            result[i] := input[i];
        } else {
            result[i] := PadString(input[i], width);
        }
        i := i + 1;
    }
}
// </vc-code>
