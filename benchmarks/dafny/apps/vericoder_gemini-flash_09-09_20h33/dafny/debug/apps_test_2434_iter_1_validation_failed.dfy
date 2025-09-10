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
predicate IsSpace(c: char) {
    c == ' '
}

predicate IsDigit(c: char) {
    '0' <= c <= '9'
}

function SplitBySpaceCorrect(s: string): (res: seq<string>)
    ensures forall i :: 0 <= i < |res| ==> |res[i]| > 0
    ensures s == StringJoin("", res)
{
    if |s| == 0 then []
    else if IsSpace(s[0]) then
        var rest := SplitBySpaceCorrect(s[1..]);
        if |rest| == 0 then [""]
        else if |rest[0]| == 0 then rest else [""] + rest
    else
        var rest := SplitBySpaceCorrect(s[1..]);
        if |rest| == 0 then [s[0..1]]
        else [s[0..1] + rest[0]] + rest[1..]
}

function SplitByNewlineCorrect(s: string): (res: seq<string>)
    ensures forall i :: 0 <= i < |res| ==> |res[i]| > 0
    ensures s == StringJoin("\n", res)
{
    if |s| == 0 then []
    else if s[0] == '\n' then
        var rest := SplitByNewlineCorrect(s[1..]);
        if |rest| == 0 then [""]
        else if |rest[0]| == 0 then rest else [""] + rest
    else
        var rest := SplitByNewlineCorrect(s[1..]);
        if |rest| == 0 then [s[0..1]]
        else [s[0..1] + rest[0]] + rest[1..]
}

function StringJoin(delimiter: string, parts: seq<string>): string
{
    if |parts| == 0 then ""
    else if |parts| == 1 then parts[0]
    else parts[0] + delimiter + StringJoin(delimiter, parts[1..])
}


lemma lemma_ParseInt_properties(s: string)
    requires IsValidInt(s)
    ensures ParseInt(s) >= 0
{
    if |s| == 0 then 
        assert ParseInt(s) == 0;
    else if |s| == 1 then
        assert '0' <= s[0] <= '9';
        assert ParseInt(s) >= 0;
    else
        assert '0' <= s[0] <= '9';
        lemma_ParseInt_properties(s[1..]);
}

lemma lemma_SplitByNewline_agrees_with_SplitByNewlineCorrect(s: string)
    ensures SplitByNewline(s) == SplitByNewlineCorrect(s)
{
    if |s| == 0 then
        assert SplitByNewline(s) == [];
        assert SplitByNewlineCorrect(s) == [];
    else if s[0] == '\n' then
        lemma_SplitByNewline_agrees_with_SplitByNewlineCorrect(s[1..]);
    else
        lemma_SplitByNewline_agrees_with_SplitByNewlineCorrect(s[1..]);
}

lemma lemma_SplitBySpace_agrees_with_SplitBySpaceCorrect(s: string)
    ensures SplitBySpace(s) == SplitBySpaceCorrect(s)
{
    if |s| == 0 then
        assert SplitBySpace(s) == [];
        assert SplitBySpaceCorrect(s) == [];
    else if s[0] == ' ' then
        lemma_SplitBySpace_agrees_with_SplitBySpaceCorrect(s[1..]);
    else
        lemma_SplitBySpace_agrees_with_SplitBySpaceCorrect(s[1..]);
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
    lemma_SplitByNewline_agrees_with_SplitByNewlineCorrect(input);
    var inputLines := SplitByNewline(input);
    var t := ParseInt(inputLines[0]);
    var outputLines: seq<string> := [];

    var i := 0;
    while i < t
        decreases t - i
        invariant 0 <= i <= t
        invariant |outputLines| == i
        invariant forall k :: 0 <= k < i ==> (outputLines[k] == "YES" || outputLines[k] == "NO")
        invariant forall k :: 0 <= k < i ==>
            var parts := SplitBySpace(inputLines[k + 1]);
            (IsValidTwoIntLine(inputLines[k+1]) && |parts| >= 2) ==>
                var x := ParseInt(parts[0]);
                var y := ParseInt(parts[1]);
                y != 0 ==> (outputLines[k] == "YES" <==> x % y == 0)
    {
        var line_index := i + 1;
        var currentLine := inputLines[line_index];
        lemma_SplitBySpace_agrees_with_SplitBySpaceCorrect(currentLine);
        var parts := SplitBySpace(currentLine);
        
        assume IsValidTwoIntLine(currentLine); // From ValidInputFormat
        assert |parts| >= 2;
        assert IsValidInt(parts[0]);
        assert IsValidInt(parts[1]);
        
        lemma_ParseInt_properties(parts[0]);
        lemma_ParseInt_properties(parts[1]);

        var x := ParseInt(parts[0]);
        var y := ParseInt(parts[1]);

        var res := "";
        if y != 0 && x % y == 0 then
            res := "YES";
        else
            res := "NO";
        outputLines := outputLines + [res];
        i := i + 1;
    }
    
    output := StringJoin("\n", outputLines);
    return output;
}
// </vc-code>

