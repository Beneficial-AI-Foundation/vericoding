// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }

function repeat_char(c: char, n: int): string
    requires n >= 0
    ensures |repeat_char(c, n)| == n
{
    if n == 0 then "" else [c] + repeat_char(c, n - 1)
}

function center_string(s: string, width: int): string
    requires |s| >= 1
    ensures |center_string(s, width)| == max(|s|, width)
    ensures if |s| < width then
        var start_pos := (width - |s| + 1) / 2;
        center_string(s, width)[start_pos..start_pos + |s|] == s
    else
        center_string(s, width) == s
{
    if |s| >= width then
        s
    else
        var padding := width - |s|;
        var left_padding := (padding + 1) / 2;
        var right_padding := padding / 2;
        repeat_char(' ', left_padding) + s + repeat_char(' ', right_padding)
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
    for i := 0 to input.Length
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
        result[i] := center_string(input[i], width);
    }
}
// </vc-code>
