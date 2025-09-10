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
function computeMax(a: int, b: int): int
{
    if a > b then a else b
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
    var dp1: array<int>;
    var dp2: array<int>;
    if n > 0 {
      dp1 := new int[n];
      dp2 := new int[n];
    } else {
      // Handle the case where n is 0. Note that ValidInput has n >= 1
      // This branch is technically unreachable due to precondition `n >= 1`
      // but Dafny requires array initialization for all control flow paths.
      dp1 := new int[1]; 
      dp2 := new int[1];
    }


    dp1[0] := h1[0];
    dp2[0] := h2[0];

    for i := 1 to n - 1
        invariant 1 <= i <= n
        invariant forall k :: 0 <= k < i ==> dp1[k] >= 0
        invariant forall k :: 0 <= k < i ==> dp2[k] >= 0
        invariant forall k :: 0 <= k < i ==> dp1[k] == maxHeightEndingInRow1(k + 1, h1, h2)
        invariant forall k :: 0 <= k < i ==> dp2[k] == maxHeightEndingInRow2(k + 1, h1, h2)
        invariant dp1.Length == n
        invariant dp2.Length == n
    {
        dp1[i] := computeMax(dp1[i-1], dp2[i-1] + h1[i]);
        dp2[i] := computeMax(dp2[i-1], dp1[i-1] + h2[i]);
    }

    result := computeMax(dp1[n-1], dp2[n-1]);
}
// </vc-code>

