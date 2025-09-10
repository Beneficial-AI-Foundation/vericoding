predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 4 &&
    (forall i :: 0 <= i < 4 ==> ValidPlayerLine(lines[i]))
}

predicate ValidPlayerLine(line: string)
{
    var parts := SplitByChar(line, ' ');
    |parts| == 2 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function ComputeResult(input: string): string
{
    var lines := SplitLines(input);
    if |lines| < 4 then ""
    else
        var player1 := ParseLine(lines[0]);
        var player2 := ParseLine(lines[1]);
        var player3 := ParseLine(lines[2]);
        var player4 := ParseLine(lines[3]);

        if |player1| != 2 || |player2| != 2 || |player3| != 2 || |player4| != 2 then ""
        else
            var a := player1[0]; // player 1 defense
            var b := player1[1]; // player 1 attack
            var c := player2[0]; // player 2 defense
            var d := player2[1]; // player 2 attack
            var x := player3[0]; // player 3 defense
            var y := player3[1]; // player 3 attack
            var z := player4[0]; // player 4 defense
            var w := player4[1]; // player 4 attack

            var Team1 := (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
            var Team2 := ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));

            if Team1 then "Team 1\n"
            else if Team2 then "Team 2\n"
            else "Draw\n"
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
{
    if input == "" then []
    else
        var lines: seq<string> := [];
        var start := 0;
        var i := 0;
        while i < |input|
            invariant 0 <= start <= i <= |input|
            // The previous invariant `forall k :: 0 <= k < |lines| ==> lines[k] == input[SplitLines.GetLineStart(input, k)..SplitLines.GetLineEnd(input, k)]`
            // is problematic because GetLineStart and GetLineEnd are not pure functions (they use `method`),
            // and their behavior depends on the loop iteration, making the invariant hard to reason about.
            // A simpler invariant for `lines` content directly refers to the `input` in terms of sub-sequences.
            // However, ensuring each line doesn't contain newlines would be a valid invariant.
            invariant NoNewlineInLines(lines)
            invariant forall k :: 0 <= k < |lines| ==> lines[k] == input[GetNthNewlineStart(input, k)..GetNthNewlineEnd(input, k)] // New invariant
        {
            if input[i] == '\n'
            {
                lines := lines + [input[start..i]];
                start := i + 1;
            }
            i := i + 1;
        }
        lines := lines + [input[start..|input|]];
        lines
}

function GetNthNewlineStart(input: string, k: nat): nat
    requires k == 0 || (exists j :: 0 <= j < |input| && input[j] == '\n')
    // This function calculates the starting index of the k-th line.
    // k=0: start of the string
    // k>0: index after the (k-1)-th newline
    ensures 0 <= GetNthNewlineStart(input, k) <= |input|
{
    if k == 0 then 0
    else
        var count := 0;
        var start := 0;
        var i := 0;
        while i < |input|
            invariant 0 <= start <= i <= |input|
            invariant 0 <= count <= k
        {
            if input[i] == '\n'
            {
                if count == k - 1 then return i + 1;
                count := count + 1;
                start := i + 1;
            }
            i := i + 1;
        }
        // If k-1 newlines are not found, it means the k-th line starts after the last known newline
        // or from the beginning if no newlines exist before k.
        // This case should ideally be prevented by preconditions or handled gracefully.
        // For ValidInput, we expect at least 4 lines, so `k` will be 0, 1, 2, or 3.
        // The last line starts from `start` if no more newlines.
        start
}

function GetNthNewlineEnd(input: string, k: nat): nat
    requires k == 0 || (exists j :: 0 <= j < |input| && input[j] == '\n')
    // This function calculates the ending index of the k-th line (exclusive).
    // k-th newline index, or end of string if it's the last line
    ensures 0 <= GetNthNewlineEnd(input, k) <= |input|
{
    var count := 0;
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant 0 <= count <= k
    {
        if input[i] == '\n'
        {
            if count == k then return i;
            count := count + 1;
        }
        i := i + 1;
    }
    |input| // If the k-th newline is not found, it means the k-th line is the last one and ends at |input|.
}

predicate NoNewlineInLines(lines: seq<string>)
{
    forall i :: 0 <= i < |lines| ==> (forall j :: 0 <= j < |lines[i]| ==> lines[i][j] != '\n')
}

function SplitByChar(s: string, c: char): seq<string>
{
    var parts: seq<string> := [];
    var start := 0;
    var i := 0; // Initialize loop variable
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant forall k :: 0 <= k < |parts| ==> (forall j :: 0 <= j < |parts[k]| ==> parts[k][j] != c)
        invariant forall k :: 0 <= k < |parts| ==> parts[k] == s[GetNthCharSplitStart(s, c, k)..GetNthCharSplitEnd(s, c, k)]
    {
        if s[i] == c
        {
            parts := parts + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    parts := parts + [s[start..|s|]];
    parts
}

function GetNthCharSplitStart(s: string, ch: char, k: nat): nat
    requires k == 0 || (exists j :: 0 <= j < |s| && s[j] == ch)
    ensures 0 <= GetNthCharSplitStart(s, ch, k) <= |s|
{
    if k == 0 then 0
    else
        var count := 0;
        var start := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= start <= i <= |s|
            invariant 0 <= count <= k
        {
            if s[i] == ch
            {
                if count == k - 1 then return i + 1;
                count := count + 1;
                start := i + 1;
            }
            i := i + 1;
        }
        start
}

function GetNthCharSplitEnd(s: string, ch: char, k: nat): nat
    requires k == 0 || (exists j :: 0 <= j < |s| && s[j] == ch)
    ensures 0 <= GetNthCharSplitEnd(s, ch, k) <= |s|
{
    var count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= count <= k
    {
        if s[i] == ch
        {
            if count == k then return i;
            count := count + 1;
        }
        i := i + 1;
    }
    |s|
}

function ParseLine(line: string): seq<int>
    requires ValidPlayerLine(line)
    ensures |ParseLine(line)| == 2
{
    var parts := SplitByChar(line, ' ');
    // These asserts are valid due to ValidPlayerLine precondition
    assert |parts| == 2;
    assert IsValidInteger(parts[0]);
    assert IsValidInteger(parts[1]);
    [ StringToInt(parts[0]), StringToInt(parts[1]) ]
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
    ensures StringToInt(s) >= 0
{
    var value := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant value >= 0
        // This invariant is tricky. It's difficult to prove `value == (if i == 0 then 0 else StringToInt(s[0..i]))`
        // without a recursive definition of StringToInt or a more complex inductive proof.
        // A simpler, yet sufficient invariant is to state that `value` is the integer representation of `s[0..i]`.
        invariant value == IntegerFromStringPrefix(s, i) // New invariant helper
    {
        value := value * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    value
}

function IntegerFromStringPrefix(s: string, length: nat): int
    requires 0 <= length <= |s|
    requires forall k :: 0 <= k < length ==> '0' <= s[k] <= '9'
    ensures IntegerFromStringPrefix(s, length) >= 0
    decreases length
{
    if length == 0 then 0
    else IntegerFromStringPrefix(s, length - 1) * 10 + (s[length-1] as int - '0' as int)
}

lemma StringToIntIsNonNegative(s: string)
    requires IsValidInteger(s)
    ensures StringToInt(s) >= 0
{
    // Proof by induction. The loop invariant `value >= 0` and the postcondition `StringToInt(s) >= 0` are sufficient.
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ComputeResult(input)
    ensures result == "Team 1\n" || result == "Team 2\n" || result == "Draw\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    // Since `ValidInput(input)` is a precondition, we know `|lines| >= 4`.
    // Also, `ValidPlayerLine(lines[i])` for `0 <= i < 4`.
    var player1 := ParseLine(lines[0]);
    var player2 := ParseLine(lines[1]);
    var player3 := ParseLine(lines[2]);
    var player4 := ParseLine(lines[3]);

    var a := player1[0]; // player 1 defense
    var b := player1[1]; // player 1 attack
    var c := player2[0]; // player 2 defense
    var d := player2[1]; // player 2 attack
    var x := player3[0]; // player 3 defense
    var y := player3[1]; // player 3 attack
    var z := player4[0]; // player 4 defense
    var w := player4[1]; // player 4 attack

    var Team1 := (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
    var Team2 := ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));

    if Team1 then result := "Team 1\n"
    else if Team2 then result := "Team 2\n"
    else result := "Draw\n";
}
// </vc-code>

