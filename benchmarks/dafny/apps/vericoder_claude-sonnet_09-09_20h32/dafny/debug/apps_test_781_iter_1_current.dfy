predicate ValidInput(input: seq<string>)
{
    |input| == 8 &&
    (forall i :: 0 <= i < 8 ==> |input[i]| == 8) &&
    (forall i, j :: 0 <= i < 8 && 0 <= j < 8 ==> input[i][j] in {'W', 'B'})
}

predicate HasAlternatingRow(row: string)
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
{
    forall k :: 1 <= k < 8 ==> row[k] != row[k-1]
}

predicate AllRowsHaveAlternatingPattern(input: seq<string>)
    requires ValidInput(input)
{
    forall i :: 0 <= i < 8 ==> HasAlternatingRow(input[i])
}

// <vc-helpers>
predicate IsValidChessboard(board: seq<string>)
    requires ValidInput(board)
{
    AllRowsHaveAlternatingPattern(board) &&
    (forall j :: 0 <= j < 8 ==> HasAlternatingColumn(board, j))
}

predicate HasAlternatingColumn(board: seq<string>, col: int)
    requires ValidInput(board)
    requires 0 <= col < 8
{
    forall k :: 1 <= k < 8 ==> board[k][col] != board[k-1][col]
}

function CountChangesForPattern(row: string, startWithW: bool): int
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
{
    if |row| == 0 then 0
    else CountChangesForPatternHelper(row, 0, startWithW)
}

function CountChangesForPatternHelper(row: string, index: int, startWithW: bool): int
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
    requires 0 <= index <= 8
    decreases 8 - index
{
    if index == 8 then 0
    else
        var expectedChar := if (startWithW && index % 2 == 0) || (!startWithW && index % 2 == 1) then 'W' else 'B';
        var change := if row[index] != expectedChar then 1 else 0;
        change + CountChangesForPatternHelper(row, index + 1, startWithW)
}

function MinChangesForBoard(board: seq<string>): int
    requires ValidInput(board)
{
    var changesW := CountChangesForBoardPattern(board, true);
    var changesB := CountChangesForBoardPattern(board, false);
    if changesW <= changesB then changesW else changesB
}

function CountChangesForBoardPattern(board: seq<string>, startWithW: bool): int
    requires ValidInput(board)
{
    CountChangesForBoardPatternHelper(board, 0, startWithW)
}

function CountChangesForBoardPatternHelper(board: seq<string>, row: int, startWithW: bool): int
    requires ValidInput(board)
    requires 0 <= row <= 8
    decreases 8 - row
{
    if row == 8 then 0
    else
        var rowStartsWithW := if (startWithW && row % 2 == 0) || (!startWithW && row % 2 == 1) then true else false;
        CountChangesForPattern(board[row], rowStartsWithW) + CountChangesForBoardPatternHelper(board, row + 1, startWithW)
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: string)
    requires ValidInput(input)
    ensures result in
// </vc-spec>
// <vc-code>
{
    var minChanges := MinChangesForBoard(input);
    result := string(minChanges as char + '0' as char);
}
// </vc-code>

