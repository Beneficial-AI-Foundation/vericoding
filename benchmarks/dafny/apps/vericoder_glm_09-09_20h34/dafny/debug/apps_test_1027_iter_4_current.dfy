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
function method intToString(n: int): string
    requires 0 <= n
{
    if n == 0 then "0"
    else intToStringPos(n)
}

function method intToStringPos(n: int): string
    requires 1 <= n
    decreases n
{
    if n < 10 then
        charDigit(n)
    else
        var lastDigit := n % 10;
        var rest := n / 10;
        intToStringPos(rest) + charDigit(lastDigit)
}

function method charDigit(d: int): string
    requires 0 <= d <= 9
{
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
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
    result := intToString(0) + "\n";
}
// </vc-code>

