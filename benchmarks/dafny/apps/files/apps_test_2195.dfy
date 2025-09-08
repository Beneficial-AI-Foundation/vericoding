Given two non-negative integers x and y, find the minimum cost to make both equal to zero using these operations:
1. Pay $a to change exactly one integer by ±1
2. Pay $b to change both integers by ±1 in the same direction

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

method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures CorrectComputation(input, output)
{
    var lines := SplitLines(input);
    var lineIndex := 0;

    if lineIndex >= |lines| { output := ""; return; }
    var t := StringToInt(lines[lineIndex]);
    lineIndex := lineIndex + 1;

    var result := "";
    var i := 0;

    while i < t && lineIndex + 1 < |lines|
        invariant 0 <= i <= t
        invariant lineIndex == 1 + 2 * i
        invariant i < t ==> lineIndex + 1 < |lines|
        invariant var outputLines := if result == "" then [] else SplitLines(result);
                  |outputLines| == i
        invariant var outputLines := if result == "" then [] else SplitLines(result);
                  forall j :: 0 <= j < |outputLines| ==> IsValidInteger(outputLines[j])
        invariant var outputLines := if result == "" then [] else SplitLines(result);
                  forall j :: 0 <= j < i && 1 + 2*j + 1 < |lines| ==>
                    var xyLine := SplitWhitespace(lines[1 + 2*j]);
                    var abLine := SplitWhitespace(lines[1 + 2*j + 1]);
                    (|xyLine| >= 2 && |abLine| >= 2) ==>
                        var x := StringToInt(xyLine[0]);
                        var y := StringToInt(xyLine[1]);
                        var a := StringToInt(abLine[0]);
                        var b := StringToInt(abLine[1]);
                        var expectedResult := if b <= 2 * a then
                            b * (if x <= y then x else y) + (if x >= y then x else y - if x <= y then x else y) * a
                        else
                            a * (x + y);
                        j < |outputLines| && StringToInt(outputLines[j]) == expectedResult
        decreases t - i
    {
        var xyLine := SplitWhitespace(lines[lineIndex]);
        var tmpCall1 := SplitWhitespace(lines[lineIndex + 1]);
        var abLine := tmpCall1;
        lineIndex := lineIndex + 2;

        if |xyLine| >= 2 && |abLine| >= 2 {
            var x := StringToInt(xyLine[0]);
            var y := StringToInt(xyLine[1]);
            var a := StringToInt(abLine[0]);
            var b := StringToInt(abLine[1]);

            var wynik: int;
            if b <= 2 * a {
                var c := if x <= y then x else y;
                var maxXY := if x >= y then x else y;
                wynik := b * c + (maxXY - c) * a;
            } else {
                wynik := a * (x + y);
            }

            var tmpCall2 := IntToString(wynik);
            if i == 0 {
                result := tmpCall2;
            } else {
                result := result + "\n" + tmpCall2;
            }
        }

        i := i + 1;
    }

    output := result;
}
