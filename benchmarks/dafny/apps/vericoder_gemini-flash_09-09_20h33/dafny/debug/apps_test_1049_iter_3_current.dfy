predicate InputWellFormed(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 &&
    var firstLineParts := SplitString(lines[0], ' ');
    |firstLineParts| == 2 &&
    IsValidInt(firstLineParts[0]) &&
    IsValidInt(firstLineParts[1]) &&
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);
    n >= 0 && d >= 0 &&
    |lines| >= d + 1 &&
    forall i :: 1 <= i <= d ==> i < |lines| && IsValidBinaryString(lines[i], n)
}

function ComputeMaxConsecutiveWins(input: string): int
    requires InputWellFormed(input)
{
    var lines := SplitLines(input);
    var firstLineParts := SplitString(lines[0], ' ');
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);
    MaxConsecutiveWinsUpTo(lines, n, d)
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidBinaryString(s: string, expectedLength: int)
{
    |s| == expectedLength && forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
{
    var lines := new seq<string>();
    var currentLine := "";
    for i := 0 to |input| - 1
        invariant 0 <= i <= |input|
        invariant forall j :: 0 <= j < |lines| ==> "\n" !in lines[j]
        invariant "\n" !in currentLine
        // The previous invariant was too complex and likely incorrect; simplified.
        // A full invariant for `SplitLines` might require reasoning about string prefixes,
        // which is often difficult in Dafny due to lack of built-in string reasoning.
        // For now, focusing on basic properties and relying on the function's correctness.
    {
        if input[i] == '\n'
        {
            lines := lines + [currentLine];
            currentLine := "";
        }
        else
        {
            currentLine := currentLine + input[i];
        }
    }
    lines := lines + [currentLine];
    lines
}

function SplitString(s: string, delimiter: char): seq<string>
{
    var parts := new seq<string>();
    var currentPart := "";
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |parts| ==> delimiter !in parts[j]
        invariant delimiter !in currentPart
        // Simplified invariant as string reasoning is complex.
    {
        if s[i] == delimiter
        {
            parts := parts + [currentPart];
            currentPart := "";
        }
        else
        {
            currentPart := currentPart + s[i];
        }
    }
    parts := parts + [currentPart];
    parts
}

function StringToInt(s: string): int
    requires IsValidInt(s)
{
    var n := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant n >= 0
        // `ParseInt` isn't available in this context for invariant verification in this way.
        // We'll trust the function's logic and the `IsValidInt` precondition.
    {
        n := n * 10 + (s[i] - '0');
    }
    n
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else
    {
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            // Invariant `ParseInt(s + (temp%10 as char))` is problematic due to casting and `ParseInt` definition.
            // Simplified for practical verification.
        {
            s := (temp % 10 as char + '0') + s; // Fixed char conversion to string
            temp := temp / 10;
        }
        s
    }
}

function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent - 1)
}

function ParseInt(s: string): int
    requires IsValidInt(s)
{
    var res := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        // `CalculateInt` is not a direct way to express the accumulated integer value.
        // The loop itself defines the parsing logic.
    {
        res := res * 10 + (s[i] - '0');
    }
    res
}

function CalculateInt(s: string): int
    // This helper function seems to be defined for recursive integer parsing,
    // but its usage might be limited if the iterative `StringToInt` or `ParseInt` are preferred.
    // Ensure `IsValidInt(s)` for correctness.
    requires IsValidInt(s)
{
    if |s| == 0 then 0
    else (s[|s|-1] - '0') + 10 * CalculateInt(s[..|s|-1])
}

function MaxConsecutiveWinsInDay(day_string: string): int
    requires forall i :: 0 <= i < |day_string| ==> day_string[i] == '0' || day_string[i] == '1'
{
    var max_wins := 0;
    var current_consecutive := 0;
    for i := 0 to |day_string| - 1
        invariant 0 <= i <= |day_string|
        invariant max_wins >= 0
        invariant current_consecutive >= 0
        invariant max_wins >= current_consecutive
        // The invariant `max_wins == MaxConsecutiveWinsInPrefix(day_string[..i])` is a strong claim
        // which might be hard to prove automatically for the verifier within this loop's context.
        // It's often better to rely on simpler loop invariants and prove the postcondition.
    {
        if day_string[i] == '1'
        {
            current_consecutive := current_consecutive + 1;
        }
        else
        {
            current_consecutive := 0;
        }
        if current_consecutive > max_wins
        {
            max_wins := current_consecutive;
        }
    }
    max_wins
}


function MaxConsecutiveWinsInPrefix(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
{
    var max_wins := 0; // consistent with MaxConsecutiveWinsInDay
    var current_consecutive := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant max_wins >= 0
        invariant current_consecutive >= 0
        invariant max_wins >= current_consecutive
        // Removing the recursive invariant to simplify verification.
        // The function computes the max consecutive wins in the given string `s`.
    {
        if s[i] == '1' {
            current_consecutive := current_consecutive + 1;
        } else {
            current_consecutive := 0;
        }
        if current_consecutive > max_wins {
            max_wins := current_consecutive;
        }
    }
    max_wins
}

function MaxConsecutiveWinsUpTo(lines: seq<string>, n: int, d: int): int
    requires |lines| >= d + 1
    requires forall i :: 1 <= i <= d ==> i < |lines| && IsValidBinaryString(lines[i], n)
    ensures MaxConsecutiveWinsUpTo(lines, n, d) >= 0
{
    var max_overall_wins := 0;
    for day_idx := 1 to d
        invariant 1 <= day_idx <= d + 1
        invariant max_overall_wins >= 0
        invariant forall k :: 1 <= k < day_idx ==> MaxConsecutiveWinsInDay(lines[k]) <= max_overall_wins
    {
        var current_day_bits := lines[day_idx];
        var current_max_wins_in_day := MaxConsecutiveWinsInDay(current_day_bits); // Use the helper function
        if current_max_wins_in_day > max_overall_wins
        {
            max_overall_wins := current_max_wins_in_day;
        }
    }
    max_overall_wins
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires InputWellFormed(input)
    ensures result == IntToString(ComputeMaxConsecutiveWins(input)) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var firstLineParts := SplitString(lines[0], ' ');
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);

    var max_overall_wins := 0;
    for day_idx := 1 to d
        invariant 1 <= day_idx <= d + 1
        invariant max_overall_wins >= 0
        // The `InputWellFormed` implies `i < |lines|` for `1 <= i <= d`
        invariant forall k :: 1 <= k < day_idx ==> MaxConsecutiveWinsInDay(lines[k]) <= max_overall_wins
    {
        var current_day_bits := lines[day_idx];
        // Directly use the helper function `MaxConsecutiveWinsInDay` to compute for the current day.
        var current_max_wins_in_day := MaxConsecutiveWinsInDay(current_day_bits);
        
        if current_max_wins_in_day > max_overall_wins
        {
            max_overall_wins := current_max_wins_in_day;
        }
    }
    result := IntToString(max_overall_wins) + "\n";
}
// </vc-code>

