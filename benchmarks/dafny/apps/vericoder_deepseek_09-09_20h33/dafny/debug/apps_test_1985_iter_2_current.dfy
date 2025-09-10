function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function computeInitialScore(pos: int, a: seq<int>, b: seq<int>): int
    requires 0 <= pos < |a|
    requires |b| > 0
{
    b[0] - sum(a[0..pos+1])
}

function computeBackwardScores(pos: int, scoreAtPos: int, a: seq<int>): set<int>
    requires 0 <= pos < |a|
    decreases pos
{
    if pos == 0 then {scoreAtPos}
    else {scoreAtPos} + computeBackwardScores(pos - 1, scoreAtPos - a[pos], a)
}

function computeForwardScores(pos: int, scoreAtPos: int, a: seq<int>): set<int>
    requires 0 <= pos < |a|
    decreases |a| - pos
{
    if pos == |a| - 1 then {}
    else computeForwardScores(pos + 1, scoreAtPos + a[pos + 1], a) + {scoreAtPos + a[pos + 1]}
}

function computeScores(pos: int, scoreAtPos: int, a: seq<int>): set<int>
    requires 0 <= pos < |a|
{
    var backwards := computeBackwardScores(pos, scoreAtPos, a);
    var forwards := computeForwardScores(pos, scoreAtPos, a);
    backwards + forwards
}

predicate isValidInitialScore(pos: int, k: int, a: seq<int>, b: seq<int>)
    requires 0 <= pos < k
    requires k > 0
    requires |a| == k
    requires |b| > 0
{
    var scores := computeScores(pos, b[0], a);
    forall j :: 0 <= j < |b| ==> b[j] in scores
}

function validInitialScores(k: int, a: seq<int>, b: seq<int>): set<int>
    requires k > 0
    requires |a| == k
    requires |b| > 0
    requires forall i :: 0 <= i < k ==> -2000 <= a[i] <= 2000
    requires forall i :: 0 <= i < |b| ==> -4000000 <= b[i] <= 4000000
{
    set i | 0 <= i < k && isValidInitialScore(i, k, a, b) :: computeInitialScore(i, a, b)
}

predicate ValidInput(k: int, n: int, a: seq<int>, b: seq<int>)
{
    k > 0 && n > 0 && |a| == k && |b| == n && n <= k &&
    (forall i, j :: 0 <= i < j < n ==> b[i] != b[j]) &&
    (forall i :: 0 <= i < k ==> -2000 <= a[i] <= 2000) &&
    (forall i :: 0 <= i < n ==> -4000000 <= b[i] <= 4000000)
}

// <vc-helpers>
lemma computeBackwardScoresRange(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    ensures forall s :: s in computeBackwardScores(pos, scoreAtPos, a) ==> s <= scoreAtPos + 2000
    decreases pos
{
    if pos > 0 {
        computeBackwardScoresRange(pos - 1, scoreAtPos - a[pos], a);
        // Show that adding a[pos] (which is <= 2000) maintains the bound
        forall s | s in computeBackwardScores(pos, scoreAtPos, a) ensures s <= scoreAtPos + 2000 {
            if s == scoreAtPos {
                // base case: scoreAtPos is <= scoreAtPos + 2000
            } else {
                // s came from recursive call, which has s <= (scoreAtPos - a[pos]) + 2000 <= scoreAtPos - a[pos] + 2000
                // Since a[pos] >= -2000, we have s <= scoreAtPos + 2000 + 2000? Need better reasoning
                // Actually: s <= (scoreAtPos - a[pos]) + 2000 = scoreAtPos + (2000 - a[pos])
                // Since a[pos] >= -2000, then -a[pos] <= 2000, so s <= scoreAtPos + 4000
                // This reveals the original lemma was incorrect!
            }
        }
    }
}

// Fix the lemma to have correct bounds
lemma computeBackwardScoresRange(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    requires forall i :: 0 <= i < |a| ==> -2000 <= a[i] <= 2000
    ensures forall s :: s in computeBackwardScores(pos, scoreAtPos, a) ==> s <= scoreAtPos + 2000 * (pos + 1)
    decreases pos
{
    if pos == 0 {
        // Only scoreAtPos itself, which is <= scoreAtPos + 2000
    } else {
        computeBackwardScoresRange(pos - 1, scoreAtPos - a[pos], a);
        // Recursive call gives: forall s in computeBackwardScores(pos-1, scoreAtPos - a[pos], a) ==> 
        // s <= (scoreAtPos - a[pos]) + 2000 * pos
        // Since a[pos] >= -2000, we have s <= scoreAtPos + 2000 + 2000 * pos = scoreAtPos + 2000 * (pos + 1)
        
        // All elements in the current set are either scoreAtPos (<= scoreAtPos + 2000*(pos+1))
        // or from the recursive call (already shown to be <= scoreAtPos + 2000*(pos+1))
    }
}

lemma computeForwardScoresRange(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    requires forall i :: 0 <= i < |a| ==> -2000 <= a[i] <= 2000
    ensures forall s :: s in computeForwardScores(pos, scoreAtPos, a) ==> s >= scoreAtPos - 2000 * (|a| - pos)
    decreases |a| - pos
{
    if pos < |a| - 1 {
        computeForwardScoresRange(pos + 1, scoreAtPos + a[pos + 1], a);
        // Recursive call gives: forall s in computeForwardScores(pos+1, scoreAtPos + a[pos+1], a) ==>
        // s >= (scoreAtPos + a[pos+1]) - 2000 * (|a| - pos - 1)
        // Since a[pos+1] >= -2000, we have s >= scoreAtPos - 2000 - 2000*(|a| - pos - 1) = scoreAtPos - 2000*(|a| - pos)
        
        // Current element is scoreAtPos + a[pos+1] >= scoreAtPos - 2000 >= scoreAtPos - 2000*(|a| - pos)
    }
}

lemma computeScoresBounded(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    requires forall i :: 0 <= i < |a| ==> -2000 <= a[i] <= 2000
    ensures forall s :: s in computeScores(pos, scoreAtPos, a) ==> 
        scoreAtPos - 2000 * (|a| - pos) <= s <= scoreAtPos + 2000 * (pos + 1)
{
    var backwards := computeBackwardScores(pos, scoreAtPos, a);
    var forwards := computeForwardScores(pos, scoreAtPos, a);
    
    computeBackwardScoresRange(pos, scoreAtPos, a);
    computeForwardScoresRange(pos, scoreAtPos, a);
}

predicate scoresContainAll(pos: int, scoreAtPos: int, a: seq<int>, b: seq<int>)
    requires 0 <= pos < |a| && |b| > 0
    requires forall i :: 0 <= i < |a| ==> -2000 <= a[i] <= 2000
{
    var scores := computeScores(pos, scoreAtPos, a);
    forall j :: 0 <= j < |b| ==> b[j] in scores
}

ghost function validScoresSet(k: int, a: seq<int>, b: seq<int>): set<int>
    requires k > 0 && |a| == k && |b| > 0
    requires forall i :: 0 <= i < k ==> -2000 <= a[i] <= 2000
{
    set i | 0 <= i < k && scoresContainAll(i, b[0], a, b) :: computeInitialScore(i, a, b)
}

lemma validSizesEqual(S: set<int>, T: set<int>)
    requires S == T
    ensures |S| == |T|
{
}

lemma ValidInputImpliesBounds(k: int, n: int, a: seq<int>, b: seq<int>)
    requires ValidInput(k, n, a, b)
    ensures forall i :: 0 <= i < k ==> -2000 <= a[i] <= 2000
    ensures |b| > 0
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(k: int, n: int, a: seq<int>, b: seq<int>) returns (result: int)
    requires ValidInput(k, n, a, b)
    ensures result >= 0
    ensures result <= k
    ensures result == |validInitialScores(k, a, b)|
// </vc-spec>
// <vc-code>
{
    ValidInputImpliesBounds(k, n, a, b);
    var count := 0;
    var i := 0;
    
    ghost var validSet := validScoresSet(k, a, b);
    
    while i < k
        invariant 0 <= i <= k
        invariant count >= 0
        invariant count == |set j | 0 <= j < i && scoresContainAll(j, b[0], a, b) :: computeInitialScore(j, a, b)|
        invariant validSet == validInitialScores(k, a, b)
    {
        var initialScore := computeInitialScore(i, a, b);
        var scores := computeScores(i, b[0], a);
        var valid := true;
        var j := 0;
        
        computeScoresBounded(i, b[0], a);
        
        while j < n
            invariant 0 <= j <= n
            invariant valid == (forall l :: 0 <= l < j ==> b[l] in scores)
        {
            if b[j] !in scores {
                valid := false;
                j := n;
            } else {
                j := j + 1;
            }
        }
        
        if valid {
            assert scoresContainAll(i, b[0], a, b);
            assert computeInitialScore(i, a, b) in validSet;
            count := count + 1;
        }
        
        i := i + 1;
    }
    
    validSizesEqual(validSet, validInitialScores(k, a, b));
    result := count;
}
// </vc-code>

