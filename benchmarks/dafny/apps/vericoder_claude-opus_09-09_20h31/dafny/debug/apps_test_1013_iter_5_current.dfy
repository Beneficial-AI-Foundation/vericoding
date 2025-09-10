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
// Function declarations for string processing
function SplitLinesFunc(s: string): seq<string>

function SplitWhitespaceFunc(s: string): seq<string>

function StringToIntFunc(s: string): int

lemma BorderCheck(input: string, n: int, m: int)
    requires |input| > 0
    requires ValidInput(input)
    requires n == GetN(input)
    requires m == GetM(input)
    ensures (exists i, j :: 0 <= i < n && 0 <= j < m && 
             GetGridCell(input, i, j) == "1" && 
             (i == 0 || j == 0 || i == n - 1 || j == m - 1)) ||
            (forall i, j :: 0 <= i < n && 0 <= j < m && 
             GetGridCell(input, i, j) == "1" ==> 
             (i != 0 && j != 0 && i != n - 1 && j != m - 1))
{
    // This lemma states that either there exists a "1" on the border,
    // or all "1"s are in the interior
}

lemma NoBorderOnes(input: string, n: int, m: int)
    requires |input| > 0
    requires ValidInput(input)
    requires n == GetN(input)
    requires m == GetM(input)
    requires forall j' :: 0 <= j' < m ==> GetGridCell(input, 0, j') != "1"
    requires forall j' :: 0 <= j' < m ==> GetGridCell(input, n - 1, j') != "1"
    requires forall i' :: 1 <= i' < n - 1 ==> GetGridCell(input, i', 0) != "1"
    requires forall i' :: 1 <= i' < n - 1 ==> GetGridCell(input, i', m - 1) != "1"
    ensures forall i', j' :: 0 <= i' < n && 0 <= j' < m && 
                            GetGridCell(input, i', j') == "1" ==>
                            (i' != 0 && j' != 0 && i' != n - 1 && j' != m - 1)
{
    // When no "1"s are on the border, all "1"s must be interior
    forall i', j' | 0 <= i' < n && 0 <= j' < m && GetGridCell(input, i', j') == "1"
        ensures i' != 0 && j' != 0 && i' != n - 1 && j' != m - 1
    {
        if i' == 0 {
            assert GetGridCell(input, 0, j') != "1";
        } else if i' == n - 1 {
            assert GetGridCell(input, n - 1, j') != "1";
        } else if j' == 0 {
            assert GetGridCell(input, i', 0) != "1";
        } else if j' == m - 1 {
            assert GetGridCell(input, i', m - 1) != "1";
        }
    }
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
    var foundOnBorder := false;
    
    // Check top row (i = 0)
    var j := 0;
    while j < m && !foundOnBorder
        invariant 0 <= j <= m
        invariant foundOnBorder ==> (exists i', j' :: 0 <= i' < n && 0 <= j' < m && 
                                     GetGridCell(input, i', j') == "1" && 
                                     (i' == 0 || j' == 0 || i' == n - 1 || j' == m - 1))
        invariant !foundOnBorder ==> (forall j' :: 0 <= j' < j ==> GetGridCell(input, 0, j') != "1")
    {
        if GetGridCell(input, 0, j) == "1" {
            foundOnBorder := true;
        }
        j := j + 1;
    }
    
    // Check bottom row (i = n - 1)
    j := 0;
    while j < m && !foundOnBorder
        invariant 0 <= j <= m
        invariant foundOnBorder ==> (exists i', j' :: 0 <= i' < n && 0 <= j' < m && 
                                     GetGridCell(input, i', j') == "1" && 
                                     (i' == 0 || j' == 0 || i' == n - 1 || j' == m - 1))
        invariant !foundOnBorder ==> (forall j' :: 0 <= j' < m ==> GetGridCell(input, 0, j') != "1")
        invariant !foundOnBorder ==> (forall j' :: 0 <= j' < j ==> GetGridCell(input, n - 1, j') != "1")
    {
        if GetGridCell(input, n - 1, j) == "1" {
            foundOnBorder := true;
        }
        j := j + 1;
    }
    
    // Check left column (j = 0), excluding corners
    var i := 1;
    while i < n - 1 && !foundOnBorder
        invariant 1 <= i <= n - 1
        invariant foundOnBorder ==> (exists i', j' :: 0 <= i' < n && 0 <= j' < m && 
                                     GetGridCell(input, i', j') == "1" && 
                                     (i' == 0 || j' == 0 || i' == n - 1 || j' == m - 1))
        invariant !foundOnBorder ==> (forall j' :: 0 <= j' < m ==> GetGridCell(input, 0, j') != "1")
        invariant !foundOnBorder ==> (forall j' :: 0 <= j' < m ==> GetGridCell(input, n - 1, j') != "1")
        invariant !foundOnBorder ==> (forall i' :: 1 <= i' < i ==> GetGridCell(input, i', 0) != "1")
    {
        if GetGridCell(input, i, 0) == "1" {
            foundOnBorder := true;
        }
        i := i + 1;
    }
    
    // Check right column (j = m - 1), excluding corners
    i := 1;
    while i < n - 1 && !foundOnBorder
        invariant 1 <= i <= n - 1
        invariant foundOnBorder ==> (exists i', j' :: 0 <= i' < n && 0 <= j' < m && 
                                     GetGridCell(input, i', j') == "1" && 
                                     (i' == 0 || j' == 0 || i' == n - 1 || j' == m - 1))
        invariant !foundOnBorder ==> (forall j' :: 0 <= j' < m ==> GetGridCell(input, 0, j') != "1")
        invariant !foundOnBorder ==> (forall j' :: 0 <= j' < m ==> GetGridCell(input, n - 1, j') != "1")
        invariant !foundOnBorder ==> (forall i' :: 1 <= i' < n - 1 ==> GetGridCell(input, i', 0) != "1")
        invariant !foundOnBorder ==> (forall i' :: 1 <= i' < i ==> GetGridCell(input, i', m - 1) != "1")
    {
        if GetGridCell(input, i, m - 1) == "1" {
            foundOnBorder := true;
        }
        i := i + 1;
    }
    
    if !foundOnBorder {
        // At this point we know:
        // - All cells in top row (i=0) don't have "1"
        // - All cells in bottom row (i=n-1) don't have "1"  
        // - All cells in left column (j=0) for i in [1, n-2] don't have "1"
        // - All cells in right column (j=m-1) for i in [1, n-2] don't have "1"
        assert forall j' :: 0 <= j' < m ==> GetGridCell(input, 0, j') != "1";
        assert forall j' :: 0 <= j' < m ==> GetGridCell(input, n - 1, j') != "1";
        assert forall i' :: 1 <= i' < n - 1 ==> GetGridCell(input, i', 0) != "1";
        assert forall i' :: 1 <= i' < n - 1 ==> GetGridCell(input, i', m - 1) != "1";
        
        NoBorderOnes(input, n, m);
        
        // Now we know all "1"s are interior
        assert forall i', j' :: 0 <= i' < n && 0 <= j' < m && 
                               GetGridCell(input, i', j') == "1" ==>
                               (i' != 0 && j' != 0 && i' != n - 1 && j' != m - 1);
    }
    
    if foundOnBorder {
        result := "2\n";
    } else {
        result := "4\n";
    }
}
// </vc-code>

