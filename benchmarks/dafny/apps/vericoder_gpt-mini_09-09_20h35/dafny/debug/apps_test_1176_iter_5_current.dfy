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
    assert s == [];
    assert sum_seq(s + [v]) == v;
    assert sum_seq(s) == 0;
  } else {
    var x := s[0];
    var rest := s[1..];
    SumSeqAppend(rest, v);
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == rest + [v];
    assert sum_seq(s + [v]) == (s + [v])[0] + sum_seq((s + [v])[1..]);
    assert sum_seq(s + [v]) == x + sum_seq(rest + [v]);
    assert sum_seq(rest + [v]) == sum_seq(rest) + v;
    assert sum_seq(s + [v]) == x + (sum_seq(rest) + v);
    assert x + (sum_seq(rest) + v) == (x + sum_seq(rest)) + v;
    assert (x + sum_seq(rest)) + v == sum_seq(s) + v;
  }
}

lemma MinSeqAppend(s: seq<int>, v: int)
  requires |s| > 0
  ensures min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s)
{
  if |s| == 1 {
    var x := s[0];
    assert s == [x];
    assert min_seq(s) == x;
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == [v];
    if x <= v {
      assert min_seq(s + [v]) == x;
      if v < min_seq(s) {
      }
      assert min_seq(s + [v]) == (if v < min_seq(s) then v else min_seq(s));
    } else {
      assert min_seq(s + [v]) == v;
      assert min_seq(s + [v]) == (if v < min_seq(s) then v else min_seq(s));
    }
  } else {
    var x := s[0];
    var rest := s[1..];
    MinSeqAppend(rest, v);
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == rest + [v];
    assert min_seq(s + [v]) == if x <= min_seq(rest + [v]) then x else min_seq(rest + [v]);
    var r := min_seq(rest);
    var rapp := min_seq(rest + [v]);
    assert rapp == (if v < r then v else r);
    var ms := min_seq(s);
    assert ms == (if x <= r then x else r);
    if v < r {
      assert rapp == v;
      if x <= v {
        assert ms == x;
        assert min_seq(s + [v]) == x;
        assert min_seq(s + [v]) == (if v < ms then v else ms);
      } else {
        assert min_seq(s + [v]) == v;
        assert (if v < ms then v else ms) == v;
        assert min_seq(s + [v]) == (if v < ms then v else ms);
      }
    } else {
      assert rapp == r;
      assert min_seq(s + [v]) == (if x <= r then x else r);
      assert min_seq(s + [v]) == ms;
      assert min_seq(s + [v]) == (if v < ms then v else ms);
    }
  }
}

lemma SumIndicatorsEqualsCount(a: seq<int>, n: int)
  requires 0 <= n <= |a|
  ensures sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then 1 else 0)) == |(set k | 0 <= k < n && a[k] < 0)|
{
  if n == 0 {
  } else {
    SumIndicatorsEqualsCount(a, n-1);
    var flag := if a[n-1] < 0 then 1 else 0;
    SumSeqAppend(seq(n-1, k requires 0 <= k < n-1 => if a[k] < 0 then 1 else 0), flag);
    if a[n-1] < 0 {
      assert |(set k | 0 <= k < n && a[k] < 0)| == |(set j | 0 <= j < n-1 && a[j] < 0) ∪ {n-1}|;
      assert forall k :: k in (set j | 0 <= j < n-1 && a[j] < 0) ==> k != n-1;
      assert |(set j | 0 <= j < n-1 && a[j] < 0) ∪ {n-1}| == |(set j | 0 <= j < n-1 && a[j] < 0)| + 1;
      assert sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then 1 else 0)) == sum_seq(seq(n-1, k requires 0 <= k < n-1 => if a[k] < 0 then 1 else 0)) + 1;
      assert sum_seq(seq(n-1, k requires 0 <= k < n-1 => if a[k] < 0 then 1 else 0)) == |(set j | 0 <= j < n-1 && a[j] < 0)|;
      assert sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then 1 else 0)) == |(set k | 0 <= k < n && a[k] < 0)|;
    } else {
      assert |(set k | 0 <= k < n && a[k] < 0)| == |(set j | 0 <= j < n-1 && a[j] < 0)|;
      assert sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then 1 else 0)) == sum_seq(seq(n-1, k requires 0 <= k < n-1 => if a[k] < 0 then 1 else 0));
      assert sum_seq(seq(n-1, k requires 0 <= k < n-1 => if a[k] < 0 then 1 else 0)) == |(set j | 0 <= j < n-1 && a[j] < 0)|;
      assert sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then 1 else 0)) == |(set k | 0 <= k < n && a[k] < 0)|;
    }
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
  var n := |a|;
  var first := if a[0] < 0 then -a[0] else a[0];
  var sum_abs := first;
  var min_abs := first;
  var count_neg := if a[0] < 0 then 1 else 0;
  ghost var b := [first];

  assert sum_seq(b) == first;
  assert min_seq(b) == first;
  if a[0] < 0 {
    assert count_neg == 1;
    assert |(set k | 0 <= k < 1 && a[k] < 0)| == 1;
  } else {
    assert count_neg == 0;
    assert |(set k | 0 <= k < 1 && a[k] < 0)| == 0;
  }

  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant b == seq(i, k requires 0 <= k < i => if a[k] < 0 then -a[k] else a[k])
    invariant sum_abs == sum_seq(b)
    invariant min_abs == min_seq(b)
    invariant count_neg == |(set k | 0 <= k < i && a[k] < 0)|
  {
    var v := if a[i] < 0 then -a[i] else a[i];
    ghost SumSeqAppend(b, v);
    ghost MinSeqAppend(b, v);
    sum_abs := sum_abs + v;
    if v < min_abs { min_abs := v; }
    if a[i] < 0 {
      count_neg := count_neg + 1;
    }
    ghost var bnew := b + [v];
    assert |bnew| == i + 1;
    assert |seq(i+1, k requires 0 <= k < i+1 => if a[k] < 0 then -a[k] else a[k])| == i + 1;
    assert forall j :: 0 <= j < i ==> bnew[j] == (if a[j] < 0 then -a[j] else a[j]);
    assert bnew[i] == v;
    b := bnew;
    i := i + 1;
  }

  assert count_neg == |(set k | 0 <= k < n && a[k] < 0)|;
  assert sum_abs == sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then -a[k] else a[k]));
  assert min_abs == min_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then -a[k] else a[k]));

  if count_neg % 2 == 0 {
    result := sum_abs;
  } else {
    result := sum_abs - 2 * min_abs;
  }
}
// </vc-code>

