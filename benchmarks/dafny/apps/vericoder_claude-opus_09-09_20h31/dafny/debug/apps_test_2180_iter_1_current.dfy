predicate ValidInput(n: int) {
    n >= 1
}

function MaxCoders(n: int): int
    requires n >= 1
{
    n * n / 2 + n * n % 2
}

predicate ValidOutputFormat(result: seq<string>, n: int) 
    requires n >= 1
{
    |result| == n + 1 &&
    result[0] == IntToString(MaxCoders(n)) &&
    (forall i :: 1 <= i <= n ==> |result[i]| == n)
}

predicate ValidCheckerboardPlacement(result: seq<string>, n: int)
    requires n >= 1
    requires ValidOutputFormat(result, n)
{
    forall i :: 1 <= i <= n ==> forall j :: 0 <= j < n ==>
        (result[i][j] == 'C' <==> 
            (if (i - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1))
}

// <vc-helpers>
function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToString(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then 
        [('0' as int + n) as char]
    else 
        IntToStringHelper(n / 10) + [('0' as int + n % 10) as char]
}

function CreateRow(n: int, rowIndex: int): string
    requires n >= 1
    requires 1 <= rowIndex <= n
    ensures |CreateRow(n, rowIndex)| == n
{
    CreateRowHelper(n, rowIndex, 0)
}

function CreateRowHelper(n: int, rowIndex: int, col: int): string
    requires n >= 1
    requires 1 <= rowIndex <= n
    requires 0 <= col <= n
    decreases n - col
    ensures |CreateRowHelper(n, rowIndex, col)| == n - col
{
    if col == n then []
    else 
        (if ((rowIndex - 1) % 2 == 0 && col % 2 == 0) || 
            ((rowIndex - 1) % 2 == 1 && col % 2 == 1) 
         then ['C'] 
         else ['.']) + CreateRowHelper(n, rowIndex, col + 1)
}

lemma CreateRowCorrect(n: int, rowIndex: int)
    requires n >= 1
    requires 1 <= rowIndex <= n
    ensures var row := CreateRow(n, rowIndex);
            |row| == n &&
            forall j :: 0 <= j < n ==>
                row[j] == 'C' <==> 
                    (if (rowIndex - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1)
{
    var row := CreateRow(n, rowIndex);
    assert row == CreateRowHelper(n, rowIndex, 0);
    CreateRowHelperCorrect(n, rowIndex, 0);
}

lemma CreateRowHelperCorrect(n: int, rowIndex: int, col: int)
    requires n >= 1
    requires 1 <= rowIndex <= n
    requires 0 <= col <= n
    decreases n - col
    ensures var row := CreateRowHelper(n, rowIndex, col);
            |row| == n - col &&
            forall j :: 0 <= j < n - col ==>
                row[j] == 'C' <==> 
                    (if (rowIndex - 1) % 2 == 0 then (col + j) % 2 == 0 
                     else (col + j) % 2 == 1)
{
    if col == n {
        // Base case: empty string
    } else {
        var rest := CreateRowHelper(n, rowIndex, col + 1);
        CreateRowHelperCorrect(n, rowIndex, col + 1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires ValidInput(n)
    ensures ValidOutputFormat(result, n)
    ensures ValidCheckerboardPlacement(result, n)
// </vc-spec>
// <vc-code>
{
    var rows: seq<string> := [IntToString(MaxCoders(n))];
    
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant |rows| == i
        invariant rows[0] == IntToString(MaxCoders(n))
        invariant forall k :: 1 <= k < i ==> |rows[k]| == n
        invariant forall k :: 1 <= k < i ==> forall j :: 0 <= j < n ==>
            rows[k][j] == 'C' <==> 
                (if (k - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1)
    {
        var row := CreateRow(n, i);
        CreateRowCorrect(n, i);
        rows := rows + [row];
        i := i + 1;
    }
    
    result := rows;
}
// </vc-code>

