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
lemma ImageSizeLeq(idx: int, k: int, a: seq<int>, b: seq<int>)
    requires 0 <= idx <= k
    requires k > 0
    requires |a| == k
    requires |b| > 0
    ensures |set i | 0 <= i < idx && isValidInitialScore(i, k, a, b) :: computeInitialScore(i, a, b)| <= idx
    decreases idx
{
    if idx == 0 {
        // empty set has cardinality 0 <= 0
    } else {
        ImageSizeLeq(idx - 1, k, a, b);
        var prev := set i | 0 <= i < idx - 1 && isValidInitialScore(i, k, a, b) :: computeInitialScore(i, a, b);
        var cur := set i | 0 <= i < idx && isValidInitialScore(i, k, a, b) :: computeInitialScore(i, a, b);
        if isValidInitialScore(idx - 1, k, a, b) {
            assert cur == prev + { computeInitialScore(idx - 1, a, b) };
            assert |prev| <= idx - 1;
            // cardinality of union with a singleton is at most previous size + 1
            assert |prev + { computeInitialScore(idx - 1, a, b)}| <= |prev| + 1;
            assert |cur| <= idx;
        } else {
            assert cur == prev;
            assert |cur| <= idx - 1;
            assert |cur| <= idx;
        }
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
  var S: set<int> := {};
  var idx := 0;
  while idx < k
    invariant 0 <= idx <= k
    invariant S == set i | 0 <= i < idx && isValidInitialScore(i, k, a, b) :: computeInitialScore(i, a, b)
    decreases k - idx
  {
    if isValidInitialScore(idx, k, a, b) {
      S := S + { computeInitialScore(idx, a, b) };
    }
    idx := idx + 1;
  }
  // At this point idx == k and S equals the comprehension for 0 <= i < idx
  ImageSizeLeq(idx, k, a, b);
  assert S == set i | 0 <= i < idx && isValidInitialScore(i, k, a, b) :: computeInitialScore(i, a, b);
  assert |S| <= idx;
  result := |S|;
}
// </vc-code>

