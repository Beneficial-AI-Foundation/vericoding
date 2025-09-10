predicate ValidInput(input: string)
{
    var lines := SplitLinesSpec(input);
    |lines| >= 2 && IsValidInteger(lines[0]) && IsValidInteger(lines[1])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitLinesSpec(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then SplitLinesSpec(s[1..])
    else 
        var nextNewline := FindNextNewline(s, 0);
        if nextNewline == -1 then [s]
        else 
            assert nextNewline >= 0 && nextNewline < |s|;
            [s[0..nextNewline]] + SplitLinesSpec(s[nextNewline+1..])
}

function FindNextNewline(s: string, start: nat): int
    requires start <= |s|
    decreases |s| - start
    ensures FindNextNewline(s, start) == -1 || (start <= FindNextNewline(s, start) < |s|)
    ensures FindNextNewline(s, start) != -1 ==> s[FindNextNewline(s, start)] == '\n'
    ensures FindNextNewline(s, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
    ensures FindNextNewline(s, start) != -1 ==> forall i :: start <= i < FindNextNewline(s, start) ==> s[i] != '\n'
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNextNewline(s, start + 1)
}

function ParseIntSpec(s: string): int
    requires IsValidInteger(s)
{
    ParseIntHelper(s, 0)
}

function ParseIntHelper(s: string, pos: nat): int
    requires pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| || s[pos] == '\n' || s[pos] == '\r' then 0
    else if '0' <= s[pos] <= '9' then
        (s[pos] as int - '0' as int) + 10 * ParseIntHelper(s, pos + 1)
    else
        ParseIntHelper(s, pos + 1)
}

// <vc-helpers>
function method ParseInt(s: string): int
    requires IsValidInteger(s)
    ensures ParseInt(s) == ParseIntSpec(s)
{
    var num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant IsValidInteger(s)
        invariant num == ParseIntSpec(s[0..i])
        invariant ParseIntSpec(s[i..]) == int.Parse(s[i..]) // This invariant helps bridge to Dafny's built-in parsing, or can be proven recursively
    {
        num := num * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    return num;
}

function method SplitLines(s: string): seq<string>
    ensures SplitLines(s) == SplitLinesSpec(s)
{
    var lines := new seq<string>();
    var start := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant lines == SplitLinesSpec(s[0..start]) // This makes reasoning about lines easier
        invariant SplitLinesSpec(s[start..i]) == "" // This represents the portion we are currently accumulating for a line
    {
        if s[i] == '\n' {
            lines := lines + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    if start < |s| {
        lines := lines + [s[start..|s|]];
    } else if |s| == 0 {
        lines := []; // Special case if input is empty
    } else if start == |s| && i == |s| && lines == [] && s[|s|-1] == '\n' {
        // If the string ends with a newline and there's nothing after it, the last line is empty.
        // This is tricky with SplitLinesSpec which handles leading/trailing newlines differently.
        // The spec implies an empty string after a final newline might yield an empty line.
        // For example, "1\n2\n" results in ["1", "2"]. "1\n" results in ["1"].
        // If the last character is a newline, and nothing follows, SplitLinesSpec doesn't add an empty string.
        // So, this case should not add an empty string.
    } else if |s| > 0 && start == 0 && i == |s| && lines == [] {
        // Covers cases like "hello" with no newlines
        lines := [s];
    }

    // Now, we need to ensure this matches the Spec precisely.
    // The previous iterative logic is not directly mirroring SplitLinesSpec due to its recursive nature.
    // Let's use the recursive spec directly for verification.
    return SplitLinesSpec(s);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures ValidInput(input) ==>
        var lines := SplitLinesSpec(input);
        var a := ParseIntSpec(lines[0]);
        var b := ParseIntSpec(lines[1]);
        (result == "LESS\n" <==> a < b) &&
        (result == "GREATER\n" <==> a > b) &&
        (result == "EQUAL\n" <==> a == b)
    ensures !ValidInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        return "";
    }

    var lines := SplitLinesSpec(input);
    var a := ParseIntSpec(lines[0]);
    var b := ParseIntSpec(lines[1]);

    if a < b {
        return "LESS\n";
    } else if a > b {
        return "GREATER\n";
    } else {
        return "EQUAL\n";
    }
}
// </vc-code>

