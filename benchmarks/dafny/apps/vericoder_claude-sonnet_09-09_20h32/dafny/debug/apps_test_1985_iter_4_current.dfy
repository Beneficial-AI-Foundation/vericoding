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
lemma ComputeScoresContainsInitialScore(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    ensures scoreAtPos in computeScores(pos, scoreAtPos, a)
{
    var backwards := computeBackwardScores(pos, scoreAtPos, a);
    var forwards := computeForwardScores(pos, scoreAtPos, a);
    assert scoreAtPos in backwards;
}

lemma InitialScoreUnique(i: int, j: int, a: seq<int>, b: seq<int>)
    requires 0 <= i < j < |a|
    requires |b| > 0
    ensures computeInitialScore(i, a, b) != computeInitialScore(j, a, b)
{
    var score_i := computeInitialScore(i, a, b);
    var score_j := computeInitialScore(j, a, b);
    
    assert score_i == b[0] - sum(a[0..i+1]);
    assert score_j == b[0] - sum(a[0..j+1]);
    
    assert sum(a[0..j+1]) == sum(a[0..i+1]) + sum(a[i+1..j+1]);
    assert sum(a[i+1..j+1]) > 0 || sum(a[i+1..j+1]) < 0 || sum(a[i+1..j+1]) == 0;
    
    if sum(a[i+1..j+1]) == 0 {
        assert false;
    }
    
    assert score_i != score_j;
}

lemma ValidInitialScoresFinite(k: int, a: seq<int>, b: seq<int>)
    requires k > 0
    requires |a| == k
    requires |b| > 0
    requires forall i :: 0 <= i < k ==> -2000 <= a[i] <= 2000
    requires forall i :: 0 <= i < |b| ==> -4000000 <= b[i] <= 4000000
    ensures |validInitialScores(k, a, b)| <= k
{
    var validSet := validInitialScores(k, a, b);
    var sourceSet := set i | 0 <= i < k && isValidInitialScore(i, k, a, b);
    
    forall i, j | i in sourceSet && j in sourceSet && i != j
        ensures computeInitialScore(i, a, b) != computeInitialScore(j, a, b)
    {
        if i < j {
            InitialScoreUnique(i, j, a, b);
        } else {
            InitialScoreUnique(j, i, a, b);
        }
    }
    
    assert |sourceSet| <= k;
    assert |validSet| <= |sourceSet|;
}

function checkValidInitialScore(pos: int, k: int, a: seq<int>, b: seq<int>): bool
    requires 0 <= pos < k
    requires k > 0
    requires |a| == k
    requires |b| > 0
    requires forall i :: 0 <= i < k ==> -2000 <= a[i] <= 2000
    requires forall i :: 0 <= i < |b| ==> -4000000 <= b[i] <= 4000000
{
    isValidInitialScore(pos, k, a, b)
}

lemma LoopInvariantMaintained(i: int, k: int, a: seq<int>, b: seq<int>, result: int)
    requires ValidInput(k, |b|, a, b)
    requires 0 <= i < k
    requires result == |set j | 0 <= j < i && isValidInitialScore(j, k, a, b) :: computeInitialScore(j, a, b)|
    ensures result + (if isValidInitialScore(i, k, a, b) then 1 else 0) == 
            |set j | 0 <= j < i + 1 && isValidInitialScore(j, k, a, b) :: computeInitialScore(j, a, b)|
{
    var oldSet := set j | 0 <= j < i && isValidInitialScore(j, k, a, b) :: computeInitialScore(j, a, b);
    var newSet := set j | 0 <= j < i + 1 && isValidInitialScore(j, k, a, b) :: computeInitialScore(j, a, b);
    
    if isValidInitialScore(i, k, a, b) {
        var newElement := computeInitialScore(i, a, b);
        assert newSet == oldSet + {newElement};
        
        forall j | 0 <= j < i && isValidInitialScore(j, k, a, b)
            ensures computeInitialScore(j, a, b) != computeInitialScore(i, a, b)
        {
            if j < i {
                InitialScoreUnique(j, i, a, b);
            }
        }
        
        assert newElement !in oldSet;
        assert |newSet| == |oldSet| + 1;
    } else {
        assert newSet == oldSet;
        assert |newSet| == |oldSet|;
    }
}
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
    result := 0;
    var i := 0;
    
    ValidInitialScoresFinite(k, a, b);
    
    while i < k
        invariant 0 <= i <= k
        invariant result >= 0
        invariant result <= i
        invariant result == |set j | 0 <= j < i && isValidInitialScore(j, k, a, b) :: computeInitialScore(j, a, b)|
    {
        LoopInvariantMaintained(i, k, a, b, result);
        
        if checkValidInitialScore(i, k, a, b) {
            result := result + 1;
        }
        i := i + 1;
    }
    
    assert result == |set j | 0 <= j < k && isValidInitialScore(j, k, a, b) :: computeInitialScore(j, a, b)|;
    assert result == |validInitialScores(k, a, b)|;
}
// </vc-code>

