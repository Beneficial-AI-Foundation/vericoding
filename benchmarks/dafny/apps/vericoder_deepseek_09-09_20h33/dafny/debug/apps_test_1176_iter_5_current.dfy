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

lemma min_seq_non_empty_proof(s: seq<int>)
  requires |s| > 0
  ensures |seq(|s|, i requires 0 <= i < |s| => if s[i] < 0 then -s[i] else s[i])| > 0
{
}

lemma sum_seq_extend(s: seq<int>, x: int)
  ensures sum_seq(s + [x]) == sum_seq(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert sum_seq([x]) == x;
    assert sum_seq([]) == 0;
  } else {
    sum_seq_extend(s[1..], x);
  }
}

lemma min_seq_extend(s: seq<int>, x: int)
  requires |s| > 0
  ensures min_seq(s + [x]) == (if x <= min_seq(s) then x else min_seq(s))
{
  if |s| == 1 {
    assert s + [x] == [s[0], x];
    var m1 := min_seq([s[0], x]);
    var m2 := if x <= s[0] then x else s[0];
    assert m1 == m2;
  } else {
    var rest := s[1..];
    min_seq_extend(rest, x);
    var min_rest_x := min_seq(rest + [x]);
    var min_rest := min_seq(rest);
    var min_s := min_seq(s);
    assert min_s == if s[0] <= min_rest then s[0] else min_rest;
    assert min_seq(s + [x]) == if s[0] <= min_rest_x then s[0] else min_rest_x;
  }
}

lemma min_seq_single(x: int)
  ensures min_seq([x]) == x
{
}

lemma min_seq_cons(x: int, s: seq<int>)
  requires |s| > 0
  ensures min_seq([x] + s) == (if x <= min_seq(s) then x else min_seq(s))
{
  min_seq_extend(s, x);
  assert [x] + s == s + [x];
}

ghost var min_abs_ghost: int
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
  var i := 0;
  var abs_seq: seq<int> := [];
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count_neg == |set j | 0 <= j < i && a[j] < 0|
    invariant sum_abs == sum_seq(abs_seq)
    invariant |abs_seq| == i
    invariant i > 0 ==> min_abs_ghost == min_seq(abs_seq)
    invariant forall k :: 0 <= k < |abs_seq| ==> abs_seq[k] == (if a[k] < 0 then -a[k] else a[k])
  {
    var abs_val := if a[i] < 0 then -a[i] else a[i];
    
    if a[i] < 0 {
      count_neg := count_neg + 1;
    }
    
    var old_abs_seq := abs_seq;
    abs_seq := abs_seq + [abs_val];
    sum_abs := sum_abs + abs_val;
    
    if i == 0 {
      min_seq_single(abs_val);
      min_abs_ghost := abs_val;
    } else {
      min_seq_extend(old_abs_seq, abs_val);
      min_abs_ghost := if abs_val <= min_abs_ghost then abs_val else min_abs_ghost;
    }
    
    i := i + 1;
  }
  
  var min_abs := min_seq(abs_seq);
  
  if count_neg % 2 == 0 {
    result := sum_abs;
  } else {
    result := sum_abs - 2 * min_abs;
  }
}
// </vc-code>

