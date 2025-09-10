predicate ValidInput(n: int, h1: seq<int>, h2: seq<int>)
{
    n >= 1 && |h1| >= n && |h2| >= n &&
    (forall i :: 0 <= i < n ==> h1[i] >= 0) &&
    (forall i :: 0 <= i < n ==> h2[i] >= 0)
}

function maxTeamHeight(n: int, h1: seq<int>, h2: seq<int>): int
    requires ValidInput(n, h1, h2)
{
    var dp1 := maxHeightEndingInRow1(n, h1, h2);
    var dp2 := maxHeightEndingInRow2(n, h1, h2);
    if dp1 > dp2 then dp1 else dp2
}

function maxHeightEndingInRow1(n: int, h1: seq<int>, h2: seq<int>): int
    requires ValidInput(n, h1, h2)
    decreases n
{
    if n == 1 then h1[0]
    else
        var prevRow2 := maxHeightEndingInRow2(n-1, h1, h2);
        var prevRow1 := maxHeightEndingInRow1(n-1, h1, h2);
        var takeFromRow2 := prevRow2 + h1[n-1];
        if takeFromRow2 > prevRow1 then takeFromRow2 else prevRow1
}

function maxHeightEndingInRow2(n: int, h1: seq<int>, h2: seq<int>): int
    requires ValidInput(n, h1, h2)
    decreases n
{
    if n == 1 then h2[0]
    else
        var prevRow1 := maxHeightEndingInRow1(n-1, h1, h2);
        var prevRow2 := maxHeightEndingInRow2(n-1, h1, h2);
        var takeFromRow1 := prevRow1 + h2[n-1];
        if takeFromRow1 > prevRow2 then takeFromRow1 else prevRow2
}

// <vc-helpers>
lemma maxHeightNonNegative(n: int, h1: seq<int>, h2: seq<int>)
    requires ValidInput(n, h1, h2)
    ensures maxHeightEndingInRow1(n, h1, h2) >= 0
    ensures maxHeightEndingInRow2(n, h1, h2) >= 0
    ensures maxTeamHeight(n, h1, h2) >= 0
    decreases n
{
    if n == 1 {
        assert h1[0] >= 0;
        assert h2[0] >= 0;
    } else {
        maxHeightNonNegative(n-1, h1, h2);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, h1: seq<int>, h2: seq<int>) returns (result: int)
    requires ValidInput(n, h1, h2)
    ensures result >= 0
    ensures result == maxTeamHeight(n, h1, h2)
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        if h1[0] > h2[0] {
            result := h1[0];
        } else {
            result := h2[0];
        }
        return;
    }

    var dp1 := new int[n];
    var dp2 := new int[n];
    
    dp1[0] := h1[0];
    dp2[0] := h2[0];
    
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> dp1[j] == maxHeightEndingInRow1(j+1, h1, h2)
        invariant forall j :: 0 <= j < i ==> dp2[j] == maxHeightEndingInRow2(j+1, h1, h2)
    {
        var takeFromRow2 := dp2[i-1] + h1[i];
        if i == 1 {
            dp1[i] := if takeFromRow2 > h1[0] then takeFromRow2 else h1[0];
        } else {
            dp1[i] := if takeFromRow2 > dp1[i-1] then takeFromRow2 else dp1[i-1];
        }
        
        var takeFromRow1 := dp1[i-1] + h2[i];
        if i == 1 {
            dp2[i] := if takeFromRow1 > h2[0] then takeFromRow1 else h2[0];
        } else {
            dp2[i] := if takeFromRow1 > dp2[i-1] then takeFromRow1 else dp2[i-1];
        }
        
        i := i + 1;
    }
    
    result := if dp1[n-1] > dp2[n-1] then dp1[n-1] else dp2[n-1];
    
    maxHeightNonNegative(n, h1, h2);
}
// </vc-code>

