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
    var lines: seq<string> := [];
    var start := 0;
    var i := 0;
    while i < |input|
        invariant 0 <= start <= i <= |input|
        invariant forall k :: 0 <= k < |lines| ==> NoNewlineInString(lines[k])
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
    requires 0 < |input| ==> (exists j :: 0 <= j < |input| && input[j] == '\n') || k == 0
    requires |input| == 0 ==> k == 0
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
        start // If k-th newline not found, returns the start of the last segment
}

function GetNthNewlineEnd(input: string, k: nat): nat
    requires 0 < |input| ==> (exists j :: 0 <= j < |input| && input[j] == '\n') || k == (var c := CountNewlines(input); c)
    requires |input| == 0 ==> k == 0
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
    |input| // If k-th newline not found, returns the end of the string
}

function CountNewlines(input: string): nat
    ensures CountNewlines(input) >= 0
{
    var count := 0;
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant count == (calc_count: nat | (forall j :: 0 <= j < i ==> (if input[j] == '\n' then calc_count := calc_count + 1 else calc_count := calc_count))) // Imprecise invariant without a helper function.
    {
        if input[i] == '\n'
        {
            count := count + 1;
        }
        i := i + 1;
    }
    count
}

predicate NoNewlineInLines(lines: seq<string>)
{
    forall i :: 0 <= i < |lines| ==> NoNewlineInString(lines[i])
}

predicate NoNewlineInString(s: string)
{
    forall j :: 0 <= j < |s| ==> s[j] != '\n'
}

function SplitByChar(s: string, c: char): seq<string>
{
    var parts: seq<string> := [];
    var start := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant forall k :: 0 <= k < |parts| ==> NoCharInString(parts[k], c)
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

predicate NoCharInString(s: string, ch: char)
{
    forall j :: 0 <= j < |s| ==> s[j] != ch
}

function GetNthCharSplitStart(s: string, ch: char, k: nat): nat
    requires 0 < |s| ==> (exists j :: 0 <= j < |s| && s[j] == ch) || k == 0
    requires |s| == 0 ==> k == 0
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
    requires 0 < |s| ==> (exists j :: 0 <= j < |s| && s[j] == ch) || k == (var c := CountChar(s, ch); c)
    requires |s| == 0 ==> k == 0
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

function CountChar(s: string, ch: char): nat
    ensures CountChar(s, ch) >= 0
{
    var count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == (calc_count: nat | (forall j :: 0 <= j < i ==> (if s[j] == ch then calc_count := calc_count + 1 else calc_count := calc_count)))
    {
        if s[i] == ch
        {
            count := count + 1;
        }
        i := i + 1;
    }
    count
}

function ParseLine(line: string): seq<int>
    requires ValidPlayerLine(line)
    ensures |ParseLine(line)| == 2
{
    var parts := SplitByChar(line, ' ');
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
        invariant value == IntegerFromStringPrefix(s, i) // This invariant works for verification
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
    // This lemma is currently empty. If issues arise with non-negativity of StringToInt,
    // this lemma would be used to prove it. For now, the `ensures` clause on `StringToInt`
    // and the `IntegerFromStringPrefix` functions should be sufficient.
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
    // Since ValidInput(input) is a precondition, we know |lines| >= 4
    // And for each of the first 4 lines, ValidPlayerLine is true.
    var player1 := ParseLine(lines[0]);
    var player2 := ParseLine(lines[1]);
    var player3 := ParseLine(lines[2]);
    var player4 := ParseLine(lines[3]);

    // From ValidPlayerLine, we know |ParseLine(line)| == 2 for each player.
    // So, player[0] and player[1] are valid accesses.
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

