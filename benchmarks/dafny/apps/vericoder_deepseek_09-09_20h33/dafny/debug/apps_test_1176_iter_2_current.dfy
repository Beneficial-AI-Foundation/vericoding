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
lemma lemma_even_negatives_property(s: seq<int>, count_neg: int, sum_abs: int, min_abs: int)
  requires |s| >= 2
  requires count_neg == |set i | 0 <= i < |s| && s[i] < 0|
  requires sum_abs == sum_seq(seq(|s|, i requires 0 <= i < |s| => if s[i] < 0 then -s[i] else s[i]))
  requires min_abs == min_seq(seq(|s|, i requires 0 <= i < |s| => if s[i] < 0 then -s[i] else s[i]))
  ensures if count_neg % 2 == 0 then true else true
{
}

lemma abs_min_positive(s: seq<int>) returns (min_abs: int)
  requires |s| > 0
  ensures min_abs == min_seq(seq(|s|, i requires 0 <= i < |s| => if s[i] < 0 then -s[i] else s[i]))
{
  min_abs := min_seq(seq(|s|, i requires 0 <= i < |s| => if s[i] < 0 then -s[i] else s[i]));
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
  var count_neg := 0;
  var sum_abs := 0;
  var min_abs := if a[0] < 0 then -a[0] else a[0];
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count_neg == |set j | 0 <= j < i && a[j] < 0|
    invariant sum_abs == sum_seq(seq(i, j requires 0 <= j < i => if a[j] < 0 then -a[j] else a[j]))
    invariant min_abs == min_seq(seq(i, j requires 0 <= j < i => if a[j] < 0 then -a[j] else a[j]))
  {
    var abs_val := if a[i] < 0 then -a[i] else a[i];
    sum_abs := sum_abs + abs_val;
    
    if a[i] < 0 {
      count_neg := count_neg + 1;
    }
    
    if abs_val < min_abs {
      min_abs := abs_val;
    }
    
    i := i + 1;
  }
  
  if count_neg % 2 == 0 {
    result := sum_abs;
  } else {
    result := sum_abs - 2 * min_abs;
  }
}
// </vc-code>

