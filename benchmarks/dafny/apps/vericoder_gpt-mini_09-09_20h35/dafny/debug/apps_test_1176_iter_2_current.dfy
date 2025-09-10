function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

function min_seq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0] else 
        var rest_min := min_seq(s[1..]);
        if s[0] <= rest_min then s[0] else rest_min
}

// <vc-helpers>
lemma SumSeqAppend(s: seq<int>, v: int)
  ensures sum_seq(s + [v]) == sum_seq(s) + v
{
  if |s| == 0 {
    // sum_seq([v]) == v and sum_seq([]) == 0 by definition
  } else {
    var x := s[0];
    var rest := s[1..];
    SumSeqAppend(rest, v);
    // By definition of sum_seq and the inductive hypothesis the result holds
  }
}

lemma MinSeqAppend(s: seq<int>, v: int)
  requires |s| > 0
  ensures min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s)
{
  if |s| == 1 {
    // For a single-element sequence s = [x], min_seq([x] + [v]) is min(x, v)
  } else {
    var x := s[0];
    var rest := s[1..];
    MinSeqAppend(rest, v);
    // By definition of min_seq and the inductive hypothesis the result holds
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| >= 2
    ensures var count_neg := |set i | 0 <= i < |a| && a[i] < 0|;
            var sum_abs := sum_seq(seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]));
            var min_abs := min_seq(seq(|a|, i requires 0 <= i < |a| => if a[i] < 0 then -a[i] else a[i]));
            result == if count_neg % 2 == 0 then sum_abs else sum_abs - 2 * min_abs
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var sumAbs := 0;
  var countNeg := 0;
  var minAbs := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant sumAbs == sum_seq(seq(i, k requires 0 <= k < i => if a[k] < 0 then -a[k] else a[k]))
    invariant countNeg == |set k | 0 <= k < i && a[k] < 0|
    invariant minAbs == (if i == 0 then 0 else min_seq(seq(i, k requires 0 <= k < i => if a[k] < 0 then -a[k] else a[k])))
    decreases |a| - i
  {
    var v := if a[i] < 0 then -a[i] else a[i];
    // update sum
    sumAbs := sumAbs + v;
    SumSeqAppend(seq(i, k requires 0 <= k < i => if a[k] < 0 then -a[k] else a[k]), v);
    // update countNeg
    if a[i] < 0 {
      countNeg := countNeg + 1;
    }
    // update minAbs
    if i == 0 {
      minAbs := v;
    } else {
      if v < minAbs {
        minAbs := v;
      }
      MinSeqAppend(seq(i, k requires 0 <= k < i => if a[k] < 0 then -a[k] else a[k]), v);
    }
    // re-establish invariants for i+1
    assert sumAbs == sum_seq(seq(i+1, k requires 0 <= k < i+1 => if a[k] < 0 then -a[k] else a[k]));
    assert minAbs == (if i+1 == 0 then 0 else min_seq(seq(i+1, k requires 0 <= k < i+1 => if a[k] < 0 then -a[k] else a[k])));
    if a[i] < 0 {
      assert countNeg == |set k | 0 <= k < i+1 && a[k] < 0|;
    } else {
      assert countNeg == |set k | 0 <= k < i+1 && a[k] < 0|;
    }
    i := i + 1;
  }
  if countNeg % 2 == 0 {
    result := sumAbs;
  } else {
    result := sumAbs - 2 * minAbs;
  }
}
// </vc-code>

