predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 &&
    IsValidInteger(lines[0]) &&
    var t := StringToInt(lines[0]);
    t >= 0 &&
    |lines| >= 1 + 2 * t &&
    forall i :: 0 <= i < t ==> 
        (1 + 2*i + 1 < |lines| && |SplitWhitespace(lines[1 + 2*i])| >= 2 &&
         1 + 2*i + 2 < |lines| && |SplitWhitespace(lines[1 + 2*i + 1])| >= 2 &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i])[0]) &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i])[1]) &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i + 1])[0]) &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i + 1])[1]) &&
         StringToInt(SplitWhitespace(lines[1 + 2*i])[0]) >= 0 &&
         StringToInt(SplitWhitespace(lines[1 + 2*i])[1]) >= 0 &&
         StringToInt(SplitWhitespace(lines[1 + 2*i + 1])[0]) >= 1 &&
         StringToInt(SplitWhitespace(lines[1 + 2*i + 1])[1]) >= 1)
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitLines(input);
    if |lines| == 0 then output == ""
    else
        var t := StringToInt(lines[0]);
        var outputLines := if output == "" then [] else SplitLines(output);
        |outputLines| == (if t == 0 then 0 else t) &&
        forall i :: 0 <= i < |outputLines| ==> IsValidInteger(outputLines[i])
}

predicate CorrectComputation(input: string, output: string)
{
    var lines := SplitLines(input);
    if |lines| == 0 then output == ""
    else
        var t := StringToInt(lines[0]);
        var outputLines := if output == "" then [] else SplitLines(output);
        |outputLines| == (if t == 0 then 0 else t) &&
        forall i :: 0 <= i < t && 1 + 2*i + 1 < |lines| ==>
            var xyLine := SplitWhitespace(lines[1 + 2*i]);
            var abLine := SplitWhitespace(lines[1 + 2*i + 1]);
            (|xyLine| >= 2 && |abLine| >= 2) ==>
                var x := StringToInt(xyLine[0]);
                var y := StringToInt(xyLine[1]);
                var a := StringToInt(abLine[0]);
                var b := StringToInt(abLine[1]);
                var expectedResult := if b <= 2 * a then
                    b * (if x <= y then x else y) + (if x >= y then x else y - if x <= y then x else y) * a
                else
                    a * (x + y);
                i < |outputLines| && StringToInt(outputLines[i]) == expectedResult
}

predicate IsValidInteger(s: string)
{
    |s| > 0 &&
    (s[0] == '-' ==> |s| > 1) &&
    forall i :: (if s[0] == '-' then 1 else 0) <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var parts := SplitByChar(s, '\n');
        seq(|parts|, i requires 0 <= i < |parts| => parts[i])
}

function SplitWhitespace(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var parts := SplitByChar(s, ' ');
        seq(|parts|, i requires 0 <= i < |parts| => parts[i])
}

function SplitByChar(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then [""]
    else if s[0] == delimiter then
        [""] + SplitByChar(s[1..], delimiter)
    else
        var rest := SplitByChar(s[1..], delimiter);
        if |rest| == 0 then [s]
        else [(s[0..1] + rest[0])] + rest[1..]
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int else 0
    else
        StringToIntHelper(s[..|s|-1]) * 10 + 
        (if '0' <= s[|s|-1] <= '9' then s[|s|-1] as int - '0' as int else 0)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [((n % 10) as char + '0' as char) as char]
}

// <vc-helpers>
function CalculateResult(x: int, y: int, a: int, b: int): int
{
    if b <= 2 * a then
        b * (if x <= y then x else y) + (if x >= y then x else y) * a - (if x <= y then 0 else x - y) * a (* Fix for the calculation - (if x <= y then x else y - if x <= y then x else y) simplifies to 0 *)
    else
        a * (x + y)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures CorrectComputation(input, output)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var t := StringToInt(lines[0]);
    var outputSeq: seq<string> := [];

    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant t == 0 || (1 + 2 * t - 1 < |lines|)
        invariant forall k :: 0 <= k < i ==> 1 + 2 * k + 1 < |lines|
        invariant |lines| >= 1 + 2 * i // This invariant implies the next.
        invariant |outputSeq| == i
        invariant forall k :: 0 <= k < i ==> IsValidInteger(outputSeq[k])
        invariant forall k :: 0 <= k < i ==>
            var xyLineK := SplitWhitespace(lines[1 + 2 * k]);
            var abLineK := SplitWhitespace(lines[1 + 2 * k + 1]);
            (|xyLineK| >= 2 && |abLineK| >= 2) ==>
                var xK := StringToInt(xyLineK[0]);
                var yK := StringToInt(xyLineK[1]);
                var aK := StringToInt(abLineK[0]);
                var bK := StringToInt(abLineK[1]);
                var expectedResultK := CalculateResult(xK, yK, aK, bK);
                StringToInt(outputSeq[k]) == expectedResultK
    {
        // Need to ensure indices are in bounds for lines access
        // These are guaranteed by ValidInput and loop invariant `1 + 2*i + 1 < |lines|`
        // We need to add the premise for the `forall k` in the invariant.
        assert ValidInput(input);
        assert (1 + 2*i < |lines|) && (1 + 2*i + 1 < |lines|);

        var xyLine := SplitWhitespace(lines[1 + 2*i]);
        var abLine := SplitWhitespace(lines[1 + 2*i + 1]);

        // Need to assert these properties based on ValidInput
        assert |xyLine| >= 2;
        assert |abLine| >= 2;
        assert IsValidInteger(xyLine[0]);
        assert IsValidInteger(xyLine[1]);
        assert IsValidInteger(abLine[0]);
        assert IsValidInteger(abLine[1]);
        
        var x := StringToInt(xyLine[0]);
        var y := StringToInt(xyLine[1]);
        var a := StringToInt(abLine[0]);
        var b := StringToInt(abLine[1]);

        var result := CalculateResult(x, y, a, b);
        outputSeq := outputSeq + [IntToString(result)];
        i := i + 1;
    }

    output := "";
    if t > 0 {
        output := outputSeq[0];
        var j := 1;
        while j < t
            invariant 1 <= j <= t
            invariant output == "" || (output == outputSeq[0] + (if j > 1 then "\n" else "") + (if j > 1 then (seq.concat(seq(j-1, k => outputSeq[k] + "\n")[..j-2] + [outputSeq[j-1]]))) else "")
            invariant output == (seq.concat(seq(j, k => outputSeq[k] + "\n"))).rev[1..].rev + outputSeq[j-1]
            invariant output == seq.concat(seq(j, k => outputSeq[k] + (if k < j-1 then "\n" else "")))
            invariant SplitLines(output) == outputSeq[..j]
            invariant forall k :: 0 <= k < j ==> IsValidInteger(outputSeq[k])
            invariant forall k :: 0 <= k < j ==>
                var currentOutputLines := SplitLines(output);
                (k < |currentOutputLines|) &&
                (var xyLineK := SplitWhitespace(lines[1 + 2*k]);
                var abLineK := SplitWhitespace(lines[1 + 2*k + 1]);
                (|xyLineK| >= 2 && |abLineK| >= 2) ==>
                    var xK := StringToInt(xyLineK[0]);
                    var yK := StringToInt(xyLineK[1]);
                    var aK := StringToInt(abLineK[0]);
                    var bK := StringToInt(abLineK[1]);
                    var expectedResultK := CalculateResult(xK, yK, aK, bK);
                    StringToInt(currentOutputLines[k]) == expectedResultK)
        {
             // To prove `SplitLines(output)` is valid, we need `output` to not be empty.
             // If j > 0, output will be non-empty (outputSeq[0] is not empty as it's an int string).
            output := output + "\n" + outputSeq[j];
            j := j + 1;
        }
    }
}
// </vc-code>

