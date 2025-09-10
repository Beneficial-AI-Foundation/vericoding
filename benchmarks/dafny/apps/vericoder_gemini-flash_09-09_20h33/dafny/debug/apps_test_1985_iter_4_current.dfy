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
        assert s[i..j] == [];
        assert sum([]) == 0;
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
            if i == pos - 1 {
                assert (scoreAtPos - a[pos]) - sumRange(a, pos - 1, pos - 1) == (scoreAtPos - a[pos]);
            }
            assert val_at_prev in computeBackwardScores(pos - 1, scoreAtPos - a[pos], a);
            calc {
                scoreAtPos - sumRange(a, i, pos);
                scoreAtPos - (sumRange(a, i, pos-1) + a[pos]);
                (scoreAtPos - a[pos]) - sumRange(a, i, pos-1);
                val_at_prev;
            }
        }
        assert scoreAtPos - sumRange(a, pos, pos) == scoreAtPos;
        assert scoreAtPos in computeBackwardScores(pos, scoreAtPos, a);
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
        assert scoreAtPos + a[pos + 1] in computeForwardScores(pos, scoreAtPos, a);
    }
}

lemma lemma_computeScores_contains_all_path_sums(pos: int, scoreAtPos: int, a: seq<int>)
    requires 0 <= pos < |a|
    ensures (for all i :: 0 <= i <= pos ==> scoreAtPos - sum(a[i..pos]) in computeScores(pos, scoreAtPos, a))
    ensures (for all i :: pos <= i < |a| ==> scoreAtPos + sum(a[pos+1..i+1]) in computeScores(pos, scoreAtPos, a))
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
    requires scoreAtPos == computeInitialScore(pos, a, b)
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

    for i := 0 to k - 1
        invariant 0 <= i <= k
        invariant initial_scores_set <= validInitialScores(k, a, b) //Subset invariant
        invariant count == |initial_scores_set|
        invariant forall prev_i :: 0 <= prev_i < i ==> (computeInitialScore(prev_i, a, b) in initial_scores_set <==> isValidInitialScore(prev_i, k, a, b))
    {
        var scoreAtCurrentPos := b[0] - sum(a[0..i+1]);

        lemma_computeScores_contains_all_path_sums(i, scoreAtCurrentPos, a);
        var all_scores := computeScores(i, scoreAtCurrentPos, a);

        var is_valid := true;
        for j := 0 to n - 1
            invariant 0 <= j <= n
            invariant is_valid ==> (forall jj :: 0 <= jj < j ==> b[jj] in all_scores)
            invariant !is_valid ==> (exists jj :: 0 <= jj < j && !(b[jj] in all_scores))
        {
            if !(b[j] in all_scores) {
                is_valid := false;
                break;
            }
            if is_valid && j == n - 1 {
                // If we reach here, it means all b[jj] for jj in 0..n-1 are in all_scores
                assert forall jj :: 0 <= jj < n ==> b[jj] in all_scores;
            }
        }

        if is_valid {
            assert isValidInitialScore(i, k, a, b);
            initial_scores_set := initial_scores_set + {scoreAtCurrentPos};
            count := count + 1;
        } else {
            assert !isValidInitialScore(i, k, a, b);
        }
    }

    assert initial_scores_set == validInitialScores(k, a, b);
    return count;
}
// </vc-code>

