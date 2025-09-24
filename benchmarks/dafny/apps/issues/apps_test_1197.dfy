// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] in {'*', '?', '0', '1', '2'}
}

predicate ValidMinesweeperField(s: string)
    requires forall i :: 0 <= i < |s| ==> s[i] in {'*', '0', '1', '2'}
{
    forall i :: 0 <= i < |s| && s[i] != '*' ==> 
        var digit := s[i] as int - '0' as int;
        var left_mine := if i > 0 && s[i-1] == '*' then 1 else 0;
        var right_mine := if i < |s| - 1 && s[i+1] == '*' then 1 else 0;
        digit == left_mine + right_mine
}

function ReplaceQuestions(s: string, replacement: string): string
    requires |s| == |replacement|
    requires forall i :: 0 <= i < |s| ==> s[i] in {'*', '?', '0', '1', '2'}
    requires forall i :: 0 <= i < |replacement| ==> replacement[i] in {'*', '0', '1', '2'}
    requires forall i :: 0 <= i < |s| ==> s[i] != '?' ==> s[i] == replacement[i]
    ensures |ReplaceQuestions(s, replacement)| == |s|
    ensures forall i :: 0 <= i < |s| ==> ReplaceQuestions(s, replacement)[i] in {'*', '0', '1', '2'}
{
    if |s| == 0 then ""
    else if s[0] == '?' then [replacement[0]] + ReplaceQuestions(s[1..], replacement[1..])
    else [s[0]] + ReplaceQuestions(s[1..], replacement[1..])
}

function CountValidMinesweeperCompletions(s: string): int
    requires ValidInput(s)
    ensures 0 <= CountValidMinesweeperCompletions(s) < 1000000007
{
    CountValidCompletionsHelper(s, 0, 1, 0, 0, 0)
}
// </vc-preamble>

// <vc-helpers>
function CountValidCompletionsHelper(s: string, pos: int, a: int, b: int, c: int, d: int): int
    requires 0 <= pos <= |s|
    requires ValidInput(s)
    requires 0 <= a && 0 <= b && 0 <= c && 0 <= d
    ensures CountValidCompletionsHelper(s, pos, a, b, c, d) >= 0
    ensures pos == |s| ==> CountValidCompletionsHelper(s, pos, a, b, c, d) == (a + b + c) % 1000000007
    ensures CountValidCompletionsHelper(s, pos, a, b, c, d) < 1000000007
    decreases |s| - pos
{
    var MOD := 1000000007;
    if pos == |s| then
        (a + b + c) % MOD
    else
        var ch := s[pos];
        if ch == '*' then
            CountValidCompletionsHelper(s, pos + 1, 0, (a + b + d) % MOD, 0, 0)
        else if ch == '?' then
            var next_a := (a + b + c) % MOD;
            var next_b := (a + b + d) % MOD;
            CountValidCompletionsHelper(s, pos + 1, next_a, next_b, 0, 0)
        else if ch == '0' then
            CountValidCompletionsHelper(s, pos + 1, 0, 0, (a + c) % MOD, 0)
        else if ch == '1' then
            CountValidCompletionsHelper(s, pos + 1, 0, 0, b % MOD, (a + c) % MOD)
        else // ch == '2'
            CountValidCompletionsHelper(s, pos + 1, 0, 0, 0, (b + d) % MOD)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 0 <= result < 1000000007
    ensures result == CountValidMinesweeperCompletions(s)
// </vc-spec>
// <vc-code>
{
    var MOD := 1000000007;
    var n := |s|;
    var a, b, c, d := 1, 0, 0, 0;

    for i := 0 to n
        invariant 0 <= a < MOD && 0 <= b < MOD && 0 <= c < MOD && 0 <= d < MOD
        invariant CountValidCompletionsHelper(s, i, a, b, c, d) == CountValidMinesweeperCompletions(s)
    {
        var ch := s[i];
        if ch == '*' {
            a, b, c, d := 0, (a + b + d) % MOD, 0, 0;
        } else if ch == '?' {
            a, b, c, d := (a + b + c) % MOD, (a + b + d) % MOD, 0, 0;
        } else if ch == '0' {
            a, b, c, d := 0, 0, (a + c) % MOD, 0;
        } else if ch == '1' {
            a, b, c, d := 0, 0, b, (a + c) % MOD;
        } else { // ch == '2'
            a, b, c, d := 0, 0, 0, (b + d) % MOD;
        }
    }

    result := (a + b + c) % MOD;
}
// </vc-code>
