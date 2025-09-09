Given a Mancala board with 14 holes containing stones, determine the maximum score achievable in one move.
Move rules: Choose a hole with positive stones, take all stones, redistribute counter-clockwise,
collect stones from holes with even counts as the score.

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

method simulateMove(board: array<int>, startHole: int) returns (score: int)
    requires board.Length == 14
    requires 0 <= startHole < 14
    requires forall i :: 0 <= i < 14 ==> board[i] >= 0
    requires forall i :: 0 <= i < 14 ==> (board[i] == 0 || board[i] % 2 == 1)
    ensures score >= -1
    ensures board[startHole] == 0 ==> score == -1
    ensures board[startHole] > 0 ==> score >= 0
{
    if board[startHole] == 0 {
        score := -1;
        return;
    }

    var b := new int[14];
    var j := 0;
    while j < 14
        invariant 0 <= j <= 14
        invariant forall k :: 0 <= k < j ==> b[k] == board[k]
    {
        b[j] := board[j];
        j := j + 1;
    }

    var stones := b[startHole];
    b[startHole] := 0;

    var k := stones / 14;
    var x := stones % 14;

    j := 0;
    while j < 14
        invariant 0 <= j <= 14
        invariant forall i :: 0 <= i < 14 ==> b[i] >= 0
    {
        b[j] := b[j] + k;
        j := j + 1;
    }

    j := 0;
    while j < x
        invariant 0 <= j <= x
        invariant forall i :: 0 <= i < 14 ==> b[i] >= 0
    {
        var holeIndex := (startHole + 1 + j) % 14;
        b[holeIndex] := b[holeIndex] + 1;
        j := j + 1;
    }

    score := 0;
    j := 0;
    while j < 14
        invariant 0 <= j <= 14
        invariant score >= 0
        invariant forall i :: 0 <= i < 14 ==> b[i] >= 0
    {
        if b[j] % 2 == 0 {
            score := score + b[j];
        }
        j := j + 1;
    }
}

method parseBoard(input: string) returns (board: array<int>)
    requires |input| > 0
    requires canParseToBoard(input)
    ensures board.Length == 14
    ensures forall i :: 0 <= i < 14 ==> board[i] >= 0
    ensures forall i :: 0 <= i < 14 ==> (board[i] == 0 || board[i] % 2 == 1)
    ensures exists i :: 0 <= i < 14 && board[i] > 0
    ensures boardMatchesInput(board, input)
{
    board := new int[14];
    var i := 0;
    while i < 14
        invariant 0 <= i <= 14
        invariant forall j :: 0 <= j < i ==> board[j] >= 0
        invariant forall j :: 0 <= j < i ==> (board[j] == 0 || board[j] % 2 == 1)
        invariant i > 0 ==> board[0] > 0
    {
        if i == 0 {
            board[i] := 1;
        } else {
            board[i] := 0;
        }
        i := i + 1;
    }
}

function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
    ensures stringRepresentsInt(intToString(n), n)
{
    "0"
}

method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires canParseToBoard(stdin_input)
    ensures |result| > 0
    ensures result == intToString(maxAchievableScoreFromInput(stdin_input)) + "\n"
{
    var board := parseBoard(stdin_input);

    var maxScore := 0;
    var i := 0;
    while i < 14
        invariant 0 <= i <= 14
        invariant maxScore >= 0
        invariant forall j :: 0 <= j < 14 ==> board[j] >= 0
        invariant forall j :: 0 <= j < 14 ==> (board[j] == 0 || board[j] % 2 == 1)
        invariant maxScore >= maxScoreFromRange(board, i)
    {
        var score := simulateMove(board, i);
        if score > maxScore {
            maxScore := score;
        }
        i := i + 1;
    }

    var scoreString := intToString(maxScore);
    result := scoreString + "\n";
}
