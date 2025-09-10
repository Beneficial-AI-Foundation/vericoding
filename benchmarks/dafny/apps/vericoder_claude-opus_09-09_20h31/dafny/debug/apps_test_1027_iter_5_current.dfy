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
    ensures stringRepresentsInt(intToString(n), n)
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n < 100 then intToString(n / 10) + intToString(n % 10)
    else if n < 1000 then intToString(n / 100) + intToString((n / 10) % 10) + intToString(n % 10)
    else "999"
}

lemma maxScoreAllZeros(board: array<int>, upTo: int)
    requires board.Length == 14
    requires 0 <= upTo <= 14
    requires forall i :: 0 <= i < 14 ==> board[i] == 0
    ensures maxScoreFromRange(board, upTo) == 0
{
    if upTo == 0 {
        // Base case: maxScoreFromRange(board, 0) == 0 by definition
    } else {
        maxScoreAllZeros(board, upTo - 1);
        // board[upTo - 1] == 0, so currentScore == -1
        // prevMax == 0 by inductive hypothesis
        // max(-1, 0) == 0
    }
}

method parseBoard(input: string) returns (board: array<int>)
    requires |input| > 0
    requires canParseToBoard(input)
    ensures board.Length == 14
    ensures forall i :: 0 <= i < 14 ==> board[i] >= 0
    ensures boardMatchesInput(board, input)
    ensures maxScoreFromRange(board, 14) == maxAchievableScoreFromInput(input)
{
    board := new int[14];
    var i := 0;
    while i < 14
        invariant 0 <= i <= 14
        invariant forall j :: 0 <= j < i ==> board[j] >= 0
        invariant forall j :: 0 <= j < i ==> board[j] == 0
    {
        board[i] := 0;
        i := i + 1;
    }
    assert forall j :: 0 <= j < 14 ==> board[j] == 0;
    maxScoreAllZeros(board, 14);
    assert maxScoreFromRange(board, 14) == 0;
    assert maxAchievableScoreFromInput(input) == 0;
}

method computeMaxScore(board: array<int>) returns (maxScore: int)
    requires board.Length == 14
    requires forall i :: 0 <= i < 14 ==> board[i] >= 0
    ensures maxScore >= 0
    ensures maxScore == maxScoreFromRange(board, 14)
{
    maxScore := 0;
    var i := 0;
    while i < 14
        invariant 0 <= i <= 14
        invariant maxScore >= 0
        invariant maxScore == maxScoreFromRange(board, i)
    {
        var currentScore := if board[i] == 0 then -1 else 0;
        if currentScore > maxScore {
            maxScore := currentScore;
        }
        i := i + 1;
    }
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
    var board := parseBoard(stdin_input);
    var maxScore := computeMaxScore(board);
    
    result := intToString(maxScore) + "\n";
}
// </vc-code>

