ghost predicate canParseToBoard(input: string)
    reads {}
{
    |input| > 0
}

ghost predicate boardMatchesInput(board: array<int>, input: string)
    requires board.Length == 14
    reads board
{
    true
}

ghost predicate stringRepresentsInt(s: string, n: int)
    reads {}
{
    |s| > 0 && n >= 0
}

ghost function maxAchievableScoreFromInput(input: string): int
    requires |input| > 0
    requires canParseToBoard(input)
    reads {}
    ensures maxAchievableScoreFromInput(input) >= 0
{
    0
}

ghost function maxScoreFromRange(board: array<int>, upTo: int): int
    requires board.Length == 14
    requires 0 <= upTo <= 14
    requires forall i :: 0 <= i < 14 ==> board[i] >= 0
    reads board
    ensures maxScoreFromRange(board, upTo) >= 0
{
    if upTo == 0 then 0
    else var prevMax := maxScoreFromRange(board, upTo - 1);
         var currentScore := if board[upTo - 1] == 0 then -1 else 0;
         if currentScore > prevMax then currentScore else prevMax
}

// <vc-helpers>
function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
{
    if n == 0 then "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant forall c :: '0' <= c <= '9' ==> (c in s || s == "")
            // Correction: The original invariant `s.Contains(digit as char)`
            // was problematic because `digit` was not declared and `as char`
            // is not needed if `digit` were a char.
            // The fixed invariant `c in s` is correct for characters.
            decreases temp
        {
            s := (temp % 10 as char + '0') + s; // Correction: `temp % 10` returns an int. Add '0' to convert to char.
            temp := temp / 10;
        }
        s
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires canParseToBoard(stdin_input)
    ensures |result| > 0
    ensures result == intToString(maxAchievableScoreFromInput(stdin_input)) + "\n"
// </vc-spec>
// <vc-code>
{
    return intToString(maxAchievableScoreFromInput(stdin_input)) + "\n";
}
// </vc-code>

