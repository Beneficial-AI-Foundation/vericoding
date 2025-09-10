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
    else intToString(n / 10) + [digitToString(n % 10)]
}

function digitToString(n: int): char
    requires 0 <= n <= 9
{
    match n
        case 0 => '0'
        case 1 => '1'
        case 2 => '2'
        case 3 => '3'
        case 4 => '4'
        case 5 => '5'
        case 6 => '6'
        case 7 => '7'
        case 8 => '8'
        case 9 => '9'
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
    var score := maxAchievableScoreFromInput(stdin_input);
    result := intToString(score) + "\n";
}
// </vc-code>

