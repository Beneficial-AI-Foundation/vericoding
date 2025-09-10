predicate ValidGrid(grid: seq<seq<int>>, n: int, m: int)
{
    |grid| == n && n > 0 && m > 0 &&
    (forall i :: 0 <= i < n ==> |grid[i]| == m) &&
    (forall i, j :: 0 <= i < n && 0 <= j < m ==> grid[i][j] == 0 || grid[i][j] == 1)
}

predicate ValidQueries(queries: seq<(int, int)>, q: int, n: int, m: int)
{
    |queries| == q && q >= 0 &&
    (forall k :: 0 <= k < q ==> 1 <= queries[k].0 <= n && 1 <= queries[k].1 <= m)
}

function ConsHelper(l: seq<int>, index: int, current: int, maxSoFar: int): int
    requires 0 <= index
    decreases |l| - index
{
    if index >= |l| then maxSoFar
    else if l[index] == 1 then
        var newCurrent := current + 1;
        var newMax := if newCurrent > maxSoFar then newCurrent else maxSoFar;
        ConsHelper(l, index + 1, newCurrent, newMax)
    else
        ConsHelper(l, index + 1, 0, maxSoFar)
}

function cons(l: seq<int>): int
{
    ConsHelper(l, 0, 0, 0)
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else 
        var rest := MaxInSeq(s[1..]);
        if s[0] > rest then s[0] else rest
}

function ComputeScore(grid: seq<seq<int>>): int
    requires |grid| > 0
    requires forall i :: 0 <= i < |grid| ==> |grid[i]| > 0
{
    var rowScores := seq(|grid|, i requires 0 <= i < |grid| => cons(grid[i]));
    MaxInSeq(rowScores)
}

// <vc-helpers>
lemma MaxInSeqLemma(s: seq<int>, i: int, maxSoFar: int)
    requires |s| > 0
    requires 0 <= i <= |s|
    requires maxSoFar == (if i == 0 then s[0] else MaxInSeq(s[0..i]))
    ensures if i < |s| then
        MaxInSeq(s[0..i+1]) == (if s[i] > maxSoFar then s[i] else maxSoFar)
    else
        MaxInSeq(s) == maxSoFar
{
    if i < |s| {
        var newMax := if s[i] > maxSoFar then s[i] else maxSoFar;
        assert s[0..i+1] == s[0..i] + [s[i]];
        assert |s[0..i]| > 0 || i > 0;
    }
}

lemma ConsHelperLemma(l: seq<int>, index: int, current: int, maxSoFar: int, actual: int)
    requires 0 <= index <= |l|
    requires actual == ConsHelper(l[index..], 0, 0, 0)
    requires maxSoFar == ConsHelper(l, index, current, maxSoFar)
    ensures ConsHelper(l, index, current, maxSoFar) ==
        if actual > maxSoFar then actual else maxSoFar
{
    if index >= |l| {
    } else if l[index] == 1 {
        var newCurrent := current + 1;
        var newMax := if newCurrent > maxSoFar then newCurrent else maxSoFar;
        ConsHelperLemma(l, index + 1, newCurrent, newMax, actual);
    } else {
        ConsHelperLemma(l, index + 1, 0, maxSoFar, actual);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, q: int, grid: seq<seq<int>>, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidGrid(grid, n, m)
    requires ValidQueries(queries, q, n, m)
    ensures |results| == q
// </vc-spec>
// <vc-code>
{
    var tempGrid := grid;
    var rowScores := new int[n];
    var maxRowScore := 0;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant rowScores.Length == n
        invariant forall j :: 0 <= j < i ==> rowScores[j] == cons(tempGrid[j])
        invariant if i > 0 then maxRowScore == MaxInSeq(rowScores[0..i]) else maxRowScore == 0
    {
        rowScores[i] := cons(tempGrid[i]);
        if i == 0 {
            maxRowScore := rowScores[0];
        } else {
            if rowScores[i] > maxRowScore {
                maxRowScore := rowScores[i];
            }
        }
        i := i + 1;
    }

    results := [];
    var k := 0;
    while k < q
        invariant |results| == k
        invariant k <= q
    {
        var query := queries[k];
        var row := query.0 - 1;
        var col := query.1 - 1;
        
        var rowSeq := tempGrid[row];
        var newRowSeq := rowSeq[..col] + [1 - rowSeq[col]] + rowSeq[col+1..];
        tempGrid := tempGrid[..row] + [newRowSeq] + tempGrid[row+1..];
        
        var oldScore := rowScores[row];
        var newScore := cons(newRowSeq);
        rowScores[row] := newScore;
        
        if newScore > maxRowScore {
            maxRowScore := newScore;
        } else if newScore < oldScore && oldScore == maxRowScore {
            maxRowScore := 0;
            var j := 0;
            while j < n
                invariant 0 <= j <= n
                invariant maxRowScore == (if j == 0 then 0 else MaxInSeq(rowScores[0..j]))
            {
                if rowScores[j] > maxRowScore {
                    maxRowScore := rowScores[j];
                }
                j := j + 1;
            }
        }
        
        results := results + [maxRowScore];
        k := k + 1;
    }
}
// </vc-code>

