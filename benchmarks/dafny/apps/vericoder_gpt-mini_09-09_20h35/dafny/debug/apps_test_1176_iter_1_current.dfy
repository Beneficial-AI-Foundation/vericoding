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
// No additional helpers required.
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
  var i := 1;
  var sumAbs := if a[0] < 0 then -a[0] else a[0];
  var countNeg := if a[0] < 0 then 1 else 0;
  var minAbs := if a[0] < 0 then -a[0] else a[0];
  while i < |a|
    invariant 0 < i <= |a|
    invariant sumAbs == sum_seq(seq(i, k requires 0 <= k < i => if a[k] < 0 then -a[k] else a[k]))
    invariant countNeg == |set k | 0 <= k < i && a[k] < 0|
    invariant minAbs == min_seq(seq(i, k requires 0 <= k < i => if a[k] < 0 then -a[k] else a[k]))
    decreases |a| - i
  {
    var v := if a[i] < 0 then -a[i] else a[i];
    sumAbs := sumAbs + v;
    if v < minAbs {
      minAbs := v;
    }
    if a[i] < 0 {
      countNeg := countNeg + 1;
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

