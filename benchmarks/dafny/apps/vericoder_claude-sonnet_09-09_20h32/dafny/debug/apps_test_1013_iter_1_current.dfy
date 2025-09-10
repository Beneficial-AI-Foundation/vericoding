predicate ValidInput(input: string)
{
    var lines := SplitLinesFunc(input);
    |lines| >= 2 &&
    var firstLine := lines[0];
    var nmParts := SplitWhitespaceFunc(firstLine);
    |nmParts| >= 2 &&
    var n := StringToIntFunc(nmParts[0]);
    var m := StringToIntFunc(nmParts[1]);
    n >= 3 && m >= 3 &&
    |lines| >= n + 1 &&
    (forall i :: 1 <= i <= n ==> 
        var rowParts := SplitWhitespaceFunc(lines[i]);
        |rowParts| >= m &&
        (forall j :: 0 <= j < m ==> rowParts[j] == "0" || rowParts[j] == "1")) &&
    (exists i, j :: 0 <= i < n && 0 <= j < m && GetGridCellHelper(lines, i, j) == "1") &&
    GetGridCellHelper(lines, 0, 0) == "0" &&
    GetGridCellHelper(lines, 0, m-1) == "0" &&
    GetGridCellHelper(lines, n-1, 0) == "0" &&
    GetGridCellHelper(lines, n-1, m-1) == "0"
}

function GetGridCellHelper(lines: seq<string>, i: int, j: int): string
    requires |lines| >= 2
    requires i >= 0 && j >= 0
    requires i + 1 < |lines|
{
    var line := lines[i + 1];
    var parts := SplitWhitespaceFunc(line);
    if j < |parts| then parts[j] else "0"
}

function GetN(input: string): int
    requires |input| > 0
    requires ValidInput(input)
    ensures GetN(input) >= 3
{
    var lines := SplitLinesFunc(input);
    var firstLine := lines[0];
    var parts := SplitWhitespaceFunc(firstLine);
    StringToIntFunc(parts[0])
}

function GetM(input: string): int
    requires |input| > 0
    requires ValidInput(input)
    ensures GetM(input) >= 3
{
    var lines := SplitLinesFunc(input);
    var firstLine := lines[0];
    var parts := SplitWhitespaceFunc(firstLine);
    StringToIntFunc(parts[1])
}

function GetGridCell(input: string, i: int, j: int): string
    requires |input| > 0
    requires ValidInput(input)
    requires 0 <= i < GetN(input)
    requires 0 <= j < GetM(input)
    ensures GetGridCell(input, i, j) == "0" || GetGridCell(input, i, j) == "1"
{
    var lines := SplitLinesFunc(input);
    var line := lines[i + 1];
    var parts := SplitWhitespaceFunc(line);
    parts[j]
}

// <vc-helpers>
lemma GridCellConsistency(input: string, i: int, j: int)
    requires |input| > 0
    requires ValidInput(input)
    requires 0 <= i < GetN(input)
    requires 0 <= j < GetM(input)
    ensures GetGridCell(input, i, j) == GetGridCellHelper(SplitLinesFunc(input), i, j)
{
    var lines := SplitLinesFunc(input);
    var n := GetN(input);
    var m := GetM(input);
    
    assert |lines| >= n + 1;
    assert i + 1 < |lines|;
    
    var line := lines[i + 1];
    var parts := SplitWhitespaceFunc(line);
    
    assert |parts| >= m;
    assert j < |parts|;
    assert GetGridCell(input, i, j) == parts[j];
    assert GetGridCellHelper(lines, i, j) == parts[j];
}

lemma BorderCellsAreZero(input: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures GetGridCell(input, 0, 0) == "0"
    ensures GetGridCell(input, 0, GetM(input) - 1) == "0"
    ensures GetGridCell(input, GetN(input) - 1, 0) == "0"
    ensures GetGridCell(input, GetN(input) - 1, GetM(input) - 1) == "0"
{
    var n := GetN(input);
    var m := GetM(input);
    var lines := SplitLinesFunc(input);
    
    GridCellConsistency(input, 0, 0);
    GridCellConsistency(input, 0, m - 1);
    GridCellConsistency(input, n - 1, 0);
    GridCellConsistency(input, n - 1, m - 1);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures result == "2\n" || result == "4\n"
    ensures result == "2\n" <==> (exists i, j :: 0 <= i < GetN(input) && 0 <= j < GetM(input) && 
                                 GetGridCell(input, i, j) == "1" && 
                                 (i == 0 || j == 0 || i == GetN(input) - 1 || j == GetM(input) - 1))
// </vc-spec>
// <vc-code>
{
    var n := GetN(input);
    var m := GetM(input);
    
    BorderCellsAreZero(input);
    
    var foundOnBorder := false;
    var i := 0;
    
    while i < n && !foundOnBorder
        invariant 0 <= i <= n
        invariant !foundOnBorder ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < m && 
                                     GetGridCell(input, ii, jj) == "1" ==>
                                     !(ii == 0 || jj == 0 || ii == n - 1 || jj == m - 1)
    {
        var j := 0;
        while j < m && !foundOnBorder
            invariant 0 <= j <= m
            invariant !foundOnBorder ==> forall jjj :: 0 <= jjj < j && 
                                         GetGridCell(input, i, jjj) == "1" ==>
                                         !(i == 0 || jjj == 0 || i == n - 1 || jjj == m - 1)
            invariant !foundOnBorder ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < m && 
                                         GetGridCell(input, ii, jj) == "1" ==>
                                         !(ii == 0 || jj == 0 || ii == n - 1 || jj == m - 1)
        {
            if GetGridCell(input, i, j) == "1" {
                if i == 0 || j == 0 || i == n - 1 || j == m - 1 {
                    foundOnBorder := true;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if foundOnBorder {
        result := "2\n";
    } else {
        result := "4\n";
    }
}
// </vc-code>

