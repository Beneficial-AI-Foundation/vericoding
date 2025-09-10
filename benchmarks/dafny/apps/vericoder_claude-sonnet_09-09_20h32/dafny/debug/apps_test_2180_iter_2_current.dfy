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
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + IntToString(n % 10)
}

function CreateRow(rowIndex: int, n: int): string
    requires n >= 1
    requires rowIndex >= 0
    ensures |CreateRow(rowIndex, n)| == n
{
    seq(n, j => if (rowIndex % 2 == 0 && j % 2 == 0) || (rowIndex % 2 == 1 && j % 2 == 1) then 'C' else '.')
}

lemma CreateRowCorrectness(rowIndex: int, n: int, j: int)
    requires n >= 1
    requires rowIndex >= 0
    requires 0 <= j < n
    ensures var row := CreateRow(rowIndex, n);
            (row[j] == 'C' <==> 
                (if rowIndex % 2 == 0 then j % 2 == 0 else j % 2 == 1))
{
    var row := CreateRow(rowIndex, n);
    assert row[j] == (if (rowIndex % 2 == 0 && j % 2 == 0) || (rowIndex % 2 == 1 && j % 2 == 1) then 'C' else '.');
}

function CreateGrid(n: int): seq<string>
    requires n >= 1
    ensures |CreateGrid(n)| == n
    ensures forall i :: 0 <= i < n ==> |CreateGrid(n)[i]| == n
{
    seq(n, i requires 0 <= i < n => CreateRow(i, n))
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
    var maxCoders := MaxCoders(n);
    var firstLine := IntToString(maxCoders);
    
    var grid := CreateGrid(n);
    
    result := [firstLine] + grid;
    
    assert |result| == n + 1;
    assert result[0] == IntToString(MaxCoders(n));
    
    forall i | 1 <= i <= n
        ensures |result[i]| == n
    {
        assert result[i] == grid[i-1];
        assert result[i] == CreateRow(i-1, n);
    }
    
    forall i | 1 <= i <= n
        ensures forall j :: 0 <= j < n ==>
            (result[i][j] == 'C' <==> 
                (if (i - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1))
    {
        forall j | 0 <= j < n
            ensures result[i][j] == 'C' <==> 
                (if (i - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1)
        {
            CreateRowCorrectness(i-1, n, j);
        }
    }
}
// </vc-code>

