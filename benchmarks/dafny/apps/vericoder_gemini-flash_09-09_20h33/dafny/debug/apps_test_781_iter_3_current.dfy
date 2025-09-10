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
predicate HasAlternatingColumn(input: seq<string>, colIndex: int)
    requires ValidInput(input)
    requires 0 <= colIndex < 8
{
    forall k :: 1 <= k < 8 ==> input[k][colIndex] != input[k-1][colIndex]
}

predicate AllColumnsHaveAlternatingPattern(input: seq<string>)
    requires ValidInput(input)
{
    forall j :: 0 <= j < 8 ==> HasAlternatingColumn(input, j)
}

predicate IsCheckerboard(input: seq<string>)
    requires ValidInput(input)
{
    AllRowsHaveAlternatingPattern(input) && AllColumnsHaveAlternatingPattern(input)
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: string)
    requires ValidInput(input)
    ensures result in
// </vc-spec>
// <vc-code>
{
    if IsCheckerboard(input) then
        result := "Checkerboard"
    else if AllRowsHaveAlternatingPattern(input) then
        result := "Rows"
    else if AllColumnsHaveAlternatingPattern(input) then
        result := "Columns"
    else
        result := "None"
}
// </vc-code>

