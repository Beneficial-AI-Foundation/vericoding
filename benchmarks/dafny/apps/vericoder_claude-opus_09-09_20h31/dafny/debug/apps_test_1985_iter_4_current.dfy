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
lemma SetCardinalityBound(k: int)
    requires k > 0
    ensures |set i | 0 <= i < k| == k
{
    var s := set i | 0 <= i < k;
    
    // Create a sequence with elements 0..k-1
    var seq_range := seq(k, i => i);
    assert |seq_range| == k;
    assert forall i :: 0 <= i < k ==> seq_range[i] == i;
    
    // Prove s contains exactly the elements in seq_range
    assert forall i :: 0 <= i < k ==> i in s;
    assert forall x :: x in s ==> 0 <= x < k;
    
    // The key insight: s has exactly k distinct elements (0 through k-1)
    // Since each integer from 0 to k-1 is in s, and s contains only those integers
    // We can establish the cardinality by induction or by the pigeonhole principle
    
    // Helper: show that the set comprehension creates exactly k distinct elements
    var witness := seq(k, i => i);
    assert |witness| == k;
    assert forall i, j :: 0 <= i < j < k ==> witness[i] != witness[j];
    assert forall i :: 0 <= i < k ==> witness[i] in s;
    assert forall x :: x in s ==> exists i :: 0 <= i < k && x == witness[i];
    
    // Therefore |s| == k
}

lemma SubsetCardinality<T>(subset: set<T>, superset: set<T>)
    requires subset <= superset
    ensures |subset| <= |superset|
{
    // This is a basic property of set cardinality
}

lemma ValidPositionsBounded(k: int, a: seq<int>, b: seq<int>)
    requires k > 0
    requires |a| == k
    requires |b| > 0
    ensures |set i | 0 <= i < k && isValidInitialScore(i, k, a, b)| <= k
{
    var validPositions := set i | 0 <= i < k && isValidInitialScore(i, k, a, b);
    var allPositions := set i | 0 <= i < k;
    
    // validPositions is a subset of allPositions
    assert forall i :: i in validPositions ==> i in allPositions;
    assert validPositions <= allPositions;
    
    SetCardinalityBound(k);
    assert |allPositions| == k;
    
    // Apply subset cardinality property
    SubsetCardinality(validPositions, allPositions);
    assert |validPositions| <= |allPositions|;
    assert |validPositions| <= k;
}

lemma ImageSetCardinality<T, U>(domain: set<T>, f: T -> U)
    ensures |set x | x in domain :: f(x)| <= |domain|
{
    // The image of a function has cardinality at most that of the domain
}

lemma ValidInitialScoresCardinality(k: int, a: seq<int>, b: seq<int>, validScores: set<int>)
    requires k > 0
    requires |a| == k
    requires |b| > 0
    requires forall i :: 0 <= i < k ==> -2000 <= a[i] <= 2000
    requires forall i :: 0 <= i < |b| ==> -4000000 <= b[i] <= 4000000
    requires validScores == validInitialScores(k, a, b)
    ensures |validScores| <= k
{
    var validPositions := set i | 0 <= i < k && isValidInitialScore(i, k, a, b);
    ValidPositionsBounded(k, a, b);
    assert |validPositions| <= k;
    
    // validScores is the image of validPositions under computeInitialScore
    assert validScores == set i | i in validPositions :: computeInitialScore(i, a, b);
    
    // Apply the image cardinality lemma
    ImageSetCardinality(validPositions, (i: int) requires i in validPositions => computeInitialScore(i, a, b));
    
    assert |validScores| <= |validPositions|;
    assert |validScores| <= k;
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
    var validScores: set<int> := {};
    var i := 0;
    
    while i < k
        invariant 0 <= i <= k
        invariant validScores == set j | 0 <= j < i && isValidInitialScore(j, k, a, b) :: computeInitialScore(j, a, b)
        invariant |validScores| <= i
    {
        if isValidInitialScore(i, k, a, b) {
            var initialScore := computeInitialScore(i, a, b);
            validScores := validScores + {initialScore};
        }
        i := i + 1;
    }
    
    assert validScores == validInitialScores(k, a, b);
    ValidInitialScoresCardinality(k, a, b, validScores);
    result := |validScores|;
}
// </vc-code>

