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
lemma maxHeightEndingInRow1_lemma(n: int, h1: seq<int>, h2: seq<int>)
    requires ValidInput(n, h1, h2)
    decreases n
    ensures maxHeightEndingInRow1(n, h1, h2) >= 0
{
    if n == 1 {
        // h1[0] >= 0 by ValidInput
    } else {
        maxHeightEndingInRow1_lemma(n-1, h1, h2);
        maxHeightEndingInRow2_lemma(n-1, h1, h2);
    }
}

lemma maxHeightEndingInRow2_lemma(n: int, h1: seq<int>, h2: seq<int>)
    requires ValidInput(n, h1, h2)
    decreases n
    ensures maxHeightEndingInRow2(n, h1, h2) >= 0
{
    if n == 1 {
        // h2[0] >= 0 by ValidInput
    } else {
        maxHeightEndingInRow1_lemma(n-1, h1, h2);
        maxHeightEndingInRow2_lemma(n-1, h1, h2);
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
        result := (if h1[0] > h2[0] then h1[0] else h2[0]);
    } else {
        var dp1_prev := 0;
        var dp2_prev := 0;
        var dp1 := h1[0];
        var dp2 := h2[0];
        
        var i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant dp1 >= 0 && dp2 >= 0
            invariant dp1 == maxHeightEndingInRow1(i+1, h1, h2)
            invariant dp2 == maxHeightEndingInRow2(i+1, h1, h2)
        {
            dp1_prev := dp1;
            dp2_prev := dp2;
            
            var new_dp1 := dp2_prev + h1[i];
            if new_dp1 > dp1_prev {
                dp1 := new_dp1;
            } else {
                dp1 := dp1_prev;
            }
            
            var new_dp2 := dp1_prev + h2[i];
            if new_dp2 > dp2_prev {
                dp2 := new_dp2;
            } else {
                dp2 := dp2_prev;
            }
            
            i := i + 1;
        }
        
        if dp1 > dp2 {
            result := dp1;
        } else {
            result := dp2;
        }
    }
}
// </vc-code>

