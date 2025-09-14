predicate ValidInputFormat(input: string)
{
    var lines := SplitByNewline(input);
    |lines| >= 1 && 
    IsValidInt(lines[0]) &&
    var t := ParseInt(lines[0]);
    t >= 0 && t + 1 <= |lines| &&
    forall i :: 1 <= i <= t ==> IsValidTwoIntLine(lines[i])
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidTwoIntLine(s: string)
{
    var parts := SplitBySpace(s);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate ValidOutputFormat(output: string, input: string)
{
    var inputLines := SplitByNewline(input);
    if |inputLines| == 0 then output == ""
    else
        var t := ParseInt(inputLines[0]);
        var outputLines := SplitByNewline(output);
        |outputLines| == t &&
        forall i :: 0 <= i < t ==> (outputLines[i] == "YES" || outputLines[i] == "NO")
}

predicate CorrectDivisibilityResults(input: string, output: string)
{
    var inputLines := SplitByNewline(input);
    if |inputLines| == 0 then output == ""
    else
        var t := ParseInt(inputLines[0]);
        var outputLines := SplitByNewline(output);
        |outputLines| == t &&
        forall i :: 0 <= i < t && i + 1 < |inputLines| ==> 
            var parts := SplitBySpace(inputLines[i + 1]);
            |parts| >= 2 ==>
                var x := ParseInt(parts[0]);
                var y := ParseInt(parts[1]);
                y != 0 ==>
                    (outputLines[i] == "YES" <==> x % y == 0)
}

function SplitByNewline(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + SplitByNewline(s[1..])
    else 
        var rest := SplitByNewline(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function SplitBySpace(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == ' ' then [""] + SplitBySpace(s[1..])
    else 
        var rest := SplitBySpace(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int else 0
    else
        if '0' <= s[0] <= '9' then
            (s[0] as int - '0' as int) * Pow10(|s| - 1) + ParseInt(s[1..])
        else 0
}

function Pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Pow10(n - 1)
}

// <vc-helpers>
function Pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Pow10(n - 1)
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int else 0
    else
        if '0' <= s[0] <= '9' then
            (s[0] as int - '0' as int) * Pow10(|s| - 1) + ParseInt(s[1..])
        else 0
}

predicate IsValidInt(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

predicate IsValidTwoIntLine(s: string)
{
    var parts := SplitBySpace(s);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate ValidInputFormat(input: string)
{
    var lines := SplitByNewline(input);
    |lines| >= 1 &&
    IsValidInt(lines[0]) &&
    var t := ParseInt(lines[0]);
    t >= 0 && t + 1 <= |lines| &&
    (forall i :: 1 <= i <= t ==> IsValidTwoIntLine(lines[i]))
}

function SplitByNewline(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then
        var rest := SplitByNewline(s[1..]);
        [""] + rest
    else
        var rest := SplitByNewline(s[1..]);
        if |rest| == 0 then [s]
        else
            var head := s[0..1] + rest[0];
            [head] + rest[1..]
}

function SplitBySpace(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == ' ' then
        var rest := SplitBySpace(s[1..]);
        [""] + rest
    else
        var rest := SplitBySpace(s[1..]);
        if |rest| == 0 then [s]
        else
            var head := s[0..1] + rest[0];
            [head] + rest[1..]
}

function SeqToString(s: seq<string>, separator: string): string
    decreases |s|
{
    if |s| == 0 then ""
    else if |s| == 1 then s[0]
    else s[0] + separator + SeqToString(s[1..], separator)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures forall i :: 0 <= i < |output| ==> output[i] in "YESNO\n"
    ensures ValidOutputFormat(output, input)
    ensures CorrectDivisibilityResults(input, output)
// </vc-spec>
// <vc-code>
{
    var inputLines := SplitByNewline(input);
    var t := ParseInt(inputLines[0]);
    var outputLines: seq<string> := [];

    var i := 0;
    while i < t
        decreases t - i
        invariant 0 <= i <= t
        invariant |outputLines| == i
        invariant forall k :: 0 <= k < i ==> (outputLines[k] == "YES" || outputLines[k] == "NO")
        invariant forall k :: 0 <= k < i && k + 1 < |inputLines| ==>
                      var parts_k := SplitBySpace(inputLines[k + 1]);
                      (|parts_k| >= 2 && IsValidInt(parts_k[0]) && IsValidInt(parts_k[1])) ==>
                          var x_k := ParseInt(parts_k[0]);
                          var y_k := ParseInt(parts_k[1]);
                          y_k != 0 ==>
                              (outputLines[k] == "YES" <==> x_k % y_k == 0)
        invariant forall k :: 0 <= k < i ==>
            var current_line_k := inputLines[k + 1];
            var parts_k := SplitBySpace(current_line_k);
            |parts_k| >= 2 && IsValidInt(parts_k[0]) && IsValidInt(parts_k[1])
            // Ensure inputs are valid for the ParseInt call to be well-defined
            invariant (t + 1) <= |inputLines| // From ValidInputFormat, and i < t implies i+1 <= t, so lineNum <= t
            invariant i + 1 < |inputLines| // Ensures inputLines[lineNum] is valid
            invariant IsValidTwoIntLine(inputLines[i+1]) // Ensures parts[0] and parts[1] are valid integers after SplitBySpace
            invariant IsValidInt(SplitBySpace(inputLines[i+1])[0])
            invariant IsValidInt(SplitBySpace(inputLines[i+1])[1])
    {
        var lineNum := i + 1;
        var currentLine := inputLines[lineNum];
        var parts := SplitBySpace(currentLine);
        var x := ParseInt(parts[0]);
        var y := ParseInt(parts[1]);

        if y != 0 && x % y == 0 {
            outputLines := outputLines + ["YES"];
        } else {
            outputLines := outputLines + ["NO"];
        }
        i := i + 1;
    }

    output := "";
    if |outputLines| > 0 {
        output := outputLines[0];
        var j := 1;
        while j < |outputLines|
            decreases |outputLines| - j
            invariant 1 <= j <= |outputLines|
            invariant output == (outputLines[0] + (if j > 0 then "\n" else "") + SeqToString(outputLines[1..j], "\n"))
            invariant forall k :: 0 <= k < j ==> (outputLines[k] == "YES" || outputLines[k] == "NO")            
        {
            output := output + "\n" + outputLines[j];
            j := j + 1;
        }
    }
}
// </vc-code>

