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
function sumRange(a: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |a|
    decreases end - start
{
    if start == end then 0
    else a[start] + sumRange(a, start + 1, end)
}

lemma lemma_sum_relation(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures sum(s[i..j]) == sumRange(s, i, j)
{
    if i == j {
        assert s[i..j] == seq<int>[];
        assert sum(seq<int>[]) == 0;
        assert sumRange(s, i, j) == 0;
    } else {
        calc {
            sum(s[i..j]);
            s[i] + sum(s[i+1..j]);
            { lemma_sum_relation(s, i+1, j); }
            s[i] + sumRange(s, i+1, j);
            sumRange(s, i, j);
        }
    }
}

lemma lemma_computeBackwardScores_property(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    ensures forall i :: 0 <= i <= pos ==> scoreAtPos - sumRange(a, i, pos) in computeBackwardScores(pos, scoreAtPos, a)
{
    if pos == 0 {
    } else {
        lemma_computeBackwardScores_property(pos - 1, scoreAtPos - a[pos], a);
        forall i | 0 <= i < pos
            ensures scoreAtPos - sumRange(a, i, pos) in computeBackwardScores(pos, scoreAtPos, a)
        {
            var val_at_prev := scoreAtPos - sumRange(a, i, pos - 1);
            assert val_at_prev in computeBackwardScores(pos - 1, scoreAtPos - a[pos], a);
            calc {
                scoreAtPos - sumRange(a, i, pos);
                scoreAtPos - (sumRange(a, i, pos-1) + a[pos]);
                (scoreAtPos - a[pos]) - sumRange(a, i, pos-1);
                val_at_prev;
            }
        }
    }
}

lemma lemma_computeForwardScores_property(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    ensures forall i :: pos < i < |a| ==> scoreAtPos + sumRange(a, pos + 1, i + 1) in computeForwardScores(pos, scoreAtPos, a)
    decreases |a| - pos
{
    if pos == |a| - 1 {
    } else {
        lemma_computeForwardScores_property(pos + 1, scoreAtPos + a[pos + 1], a);
        forall i | pos + 1 < i < |a|
            ensures scoreAtPos + sumRange(a, pos + 1, i + 1) in computeForwardScores(pos, scoreAtPos, a)
        {
            var val_for_next := (scoreAtPos + a[pos + 1]) + sumRange(a, pos + 2, i + 1);
            assert val_for_next in computeForwardScores(pos + 1, scoreAtPos + a[pos + 1], a);
            assert sumRange(a, pos + 1, i + 1) == a[pos + 1] + sumRange(a, pos + 2, i + 1);
        }
    }
}

lemma lemma_computeScores_contains_all_path_sums(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    ensures (forall i :: 0 <= i <= pos ==> scoreAtPos - sum(a[i..pos]) in computeScores(pos, scoreAtPos, a))
    ensures (forall i :: pos <= i < |a| ==> scoreAtPos + sum(a[pos+1..i+1]) in computeScores(pos, scoreAtPos, a))
{
    lemma_computeBackwardScores_property(pos, scoreAtPos, a);
    forall i | 0 <= i <= pos
        ensures scoreAtPos - sum(a[i..pos]) in computeScores(pos, scoreAtPos, a)
    {
        lemma_sum_relation(a, i, pos);
        assert scoreAtPos - sumRange(a, i, pos) in computeBackwardScores(pos, scoreAtPos, a);
    }
    lemma_computeForwardScores_property(pos, scoreAtPos, a);
    forall i | pos < i < |a|
        ensures scoreAtPos + sum(a[pos+1..i+1]) in computeScores(pos, scoreAtPos, a)
    {
        lemma_sum_relation(a, pos+1, i+1);
        assert scoreAtPos + sumRange(a, pos+1, i+1) in computeForwardScores(pos, scoreAtPos, a);
    }
    assert scoreAtPos in computeScores(pos, scoreAtPos, a);
}

lemma lemma_path_sums_for_j_in_b(pos: int, scoreAtPos: int, a: seq<int>, b: seq<int>, j: int)
    requires 0 <= pos < |a|
    requires 0 <= j < |b|
    requires isValidInitialScore(pos, |a|, a, b) // This allows relating b[j] to path sums
    ensures b[j] in computeScores(pos, scoreAtPos, a)
{
    lemma_computeScores_contains_all_path_sums(pos, scoreAtPos, a);
}

predicate exists_suitable_path_sum(pos: int, k: int, a: seq<int>, b: seq<int>, j: int)
    requires 0 <= pos < k
    requires k > 0
    requires |a| == k
    requires |b| > 0
    requires 0 <= j < |b|
{
    var scoreAtPos := computeInitialScore(pos, a, b);
    var scores := computeScores(pos, scoreAtPos, a);
    b[j] in scores
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
    var count := 0;
    var initial_scores_set := {};

    // Iterate through all possible initial positions 'i' from 'a'
    for i := 0 to k - 1
        invariant 0 <= i <= k
        invariant initial_scores_set <= validInitialScores(k, a, b)
        invariant count == |initial_scores_set|
    {
        // Calculate the score at the current position 'i' based on 'b[0]' and 'a'
        var scoreAtCurrentPos := b[0] - sum(a[0..i+1]);

        // Compute all reachable scores from this initial position
        // This set 'all_scores' will contain values of the form:
        // b[0] - sum(a[0..i+1]) - sum_{p=j..i-1}(a[p])  (for j < i)  -> b[0] - sum(a[0..i+1]) - (sum(a[0..i])-sum(a[0..j]))
        // b[0] - sum(a[0..i+1]) + sum_{p=i+1..j}(a[p]) (for j > i)
        lemma_computeScores_contains_all_path_sums(i, scoreAtCurrentPos, a);
        var all_scores := computeScores(i, scoreAtCurrentPos, a);

        var is_valid := true;
        // Check if all elements 'b[j]' exist within the computed 'all_scores'
        for j := 0 to n - 1
            invariant 0 <= j <= n
            invariant is_valid ==> (forall jj :: 0 <= jj < j ==> b[jj] in all_scores)
        {
            if !(b[j] in all_scores) {
                is_valid := false;
                break;
            }
        }

        // If all 'b[j]' are present, then this 'scoreAtCurrentPos' is a valid initial score
        if is_valid {
            initial_scores_set := initial_scores_set + {scoreAtCurrentPos};
            count := count + 1;
        }
    }

    // Since b contains distinct elements (from ValidInput) and the problem statement
    // implies we are counting *distinct* initial scores, the size of the set
    // `initial_scores_set` directly gives the number of valid initial scores.
    // The proof that `initial_scores_set` actually equals `validInitialScores(k,a,b)`
    // is critical here.
    assert initial_scores_set == validInitialScores(k, a, b);
    return count;
}
// </vc-code>

