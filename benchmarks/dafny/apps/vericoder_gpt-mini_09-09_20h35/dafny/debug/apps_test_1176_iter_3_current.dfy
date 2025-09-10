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
    assert sum_seq(s + [v]) == sum_seq(s) + v;
  } else {
    var x := s[0];
    var rest := s[1..];
    SumSeqAppend(rest, v);
    // unfold definitions via indexing facts
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == rest + [v];
    assert sum_seq(s + [v]) == (s + [v])[0] + sum_seq((s + [v])[1..]);
    assert sum_seq(s + [v]) == x + sum_seq(rest + [v]);
    assert sum_seq(rest + [v]) == sum_seq(rest) + v;
    assert sum_seq(s + [v]) == x + (sum_seq(rest) + v);
    assert x + (sum_seq(rest) + v) == (x + sum_seq(rest)) + v;
    assert (x + sum_seq(rest)) + v == sum_seq(s) + v;
    assert sum_seq(s + [v]) == sum_seq(s) + v;
  }
}

lemma MinSeqAppend(s: seq<int>, v: int)
  requires |s| > 0
  ensures min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s)
{
  if |s| == 1 {
    var x := s[0];
    // s = [x]
    // min_seq([x] + [v]) == if v < x then v else x
    assert s == [x];
    assert min_seq(s) == x;
    assert min_seq(s + [v]) == (s + [v])[0] + 0 || true; // harmless to help unfolding
    // unfold min_seq for two-element sequence
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == [v];
    // min_seq([x, v]) == if x <= v then x else v
    if x <= v {
      assert min_seq(s + [v]) == x;
      assert (if v < min_seq(s) then v else min_seq(s)) == (if v < x then v else x);
      // since x <= v, v < x is false, so RHS == x
      assert (if v < x then v else x) == x;
      assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
    } else {
      // x > v
      assert min_seq(s + [v]) == v;
      if v < x {
        assert (if v < min_seq(s) then v else min_seq(s)) == v;
      } else {
        assert (if v < min_seq(s) then v else min_seq(s)) == x;
      }
      assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
    }
  } else {
    var x := s[0];
    var rest := s[1..];
    MinSeqAppend(rest, v);
    // Unfold min_seq(s + [v])
    // (s + [v])[0] == x
    // (s + [v])[1..] == rest + [v]
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == rest + [v];
    assert min_seq(s + [v]) == if x <= min_seq(rest + [v]) then x else min_seq(rest + [v]);
    // By inductive hypothesis min_seq(rest + [v]) == if v < min_seq(rest) then v else min_seq(rest)
    var restMin := min_seq(rest);
    var restMinApp := min_seq(rest + [v]);
    assert restMinApp == (if v < restMin then v else restMin);
    // Now consider cases on relation of x and restMinApp vs restMin to show desired equality
    if v < (if x <= restMin then x else restMin) {
      // v < min_seq(s)
      // Need to show min_seq(s + [v]) == v
      // From above, min_seq(s + [v]) == if x <= restMinApp then x else restMinApp
      if x <= restMinApp {
        // then min_seq(s + [v]) == x
        // but v < min_seq(s) and min_seq(s) == if x <= restMin then x else restMin
        // In this subcase we must have contradiction or x == v conditions; handle uniformly by chaining:
        // We can reason from restMinApp == if v < restMin then v else restMin
        // If x <= restMinApp and v < (if x <= restMin then x else restMin), it's possible only if v < x and restMinApp == v, so min_seq(s + [v]) == x or v; handle by direct case analysis below.
        // Do direct case-splitting on whether v < restMin
        if v < restMin {
          // restMinApp == v, so x <= restMinApp implies x <= v contradicts v < x; hence cannot happen
          reveal; // no-op to stress solver
        }
      }
    }
    // Simpler approach: show equality holds by expanding both sides and using IH; do case on whether v < restMin
    if v < restMin {
      // restMinApp == v
      // then min_seq(s + [v]) == if x <= v then x else v
      if x <= v {
        // min_seq(s + [v]) == x
        // min_seq(s) == if x <= restMin then x else restMin
        // since v < restMin and x <= v implies x <= restMin, so min_seq(s) == x
        assert min_seq(s + [v]) == x;
        assert (if v < min_seq(s) then v else min_seq(s)) == (if v < x then v else x);
        // since x <= v, v < x is false, RHS == x
        assert (if v < x then v else x) == x;
        assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
      } else {
        // x > v
        // min_seq(s + [v]) == v
        // min_seq(s) == if x <= restMin then x else restMin
        // since v < restMin, restMin >= v+1 possibly; but x > v doesn't decide relation to restMin. However:
        // If x <= restMin then min_seq(s) == x (> v), so RHS == v.
        // Else min_seq(s) == restMin (>= v+1), so RHS == v.
        assert min_seq(s + [v]) == v;
        assert (if v < min_seq(s) then v else min_seq(s)) == v;
        assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
      }
    } else {
      // v >= restMin, so restMinApp == restMin
      // then min_seq(s + [v]) == if x <= restMin then x else restMin == min_seq(s)
      assert restMinApp == restMin;
      assert min_seq(s + [v]) == (if x <= restMin then x else restMin);
      assert (if v < min_seq(s) then v else min_seq(s)) == (if v < (if x <= restMin then x else restMin) then v else (if x <= restMin then x else restMin));
      // Since restMinApp == restMin and min_seq(s) == (if x <= restMin then x else restMin), and v >= restMin,
      // v < min_seq(s) is false if min_seq(s) == restMin, and if min_seq(s) == x then v < x might be false/true but consistency holds.
      // In any case, both sides equal min_seq(s) when v >= restMin, so:
      assert min_seq(s + [v]) == min_seq(s);
      assert min_seq(s + [v]) == (if v < min_seq(s) then v else min_seq(s));
    }
  }
}

lemma SumIndicatorsEqualsCount(a: seq<int>, n: int)
  requires 0 <= n <= |a|
  ensures sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then 1 else 0)) == |set k | 0 <= k < n && a[k] < 0|
{
  if n == 0 {
    // both sides are 0
  } else {
    SumIndicatorsEqualsCount(a, n-1);
    var flag := if a[n-1] < 0 then 1 else 0;
    // apply SumSeqAppend to get sum relation
    SumSeqAppend(seq(n-1, k requires 0 <= k < n-1 => if a[k] < 0 then 1 else 0), flag);
    // reason about set cardinality growth
    if a[n-1] < 0 {
      // the set for length n equals previous set union {n-1} and n-1 not in previous set
      assert |set k | 0 <= k < n && a[k] < 0| == |set k |
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
lemma SumSeqAppend(s: seq<int>, v: int)
  ensures sum_seq(s + [v]) == sum_seq(s) + v
{
  if |s| == 0 {
    assert s == [];
    assert sum_seq(s + [v]) == v;
    assert sum_seq(s) == 0;
    assert sum_seq(s + [v]) == sum_seq(s) + v;
  } else {
    var x := s[0];
    var rest := s[1..];
    SumSeqAppend(rest, v);
    // unfold definitions via indexing facts
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == rest + [v];
    assert sum_seq(s + [v]) == (s + [v])[0] + sum_seq((s + [v])[1..]);
    assert sum_seq(s + [v]) == x + sum_seq(rest + [v]);
    assert sum_seq(rest + [v]) == sum_seq(rest) + v;
    assert sum_seq(s + [v]) == x + (sum_seq(rest) + v);
    assert x + (sum_seq(rest) + v) == (x + sum_seq(rest)) + v;
    assert (x + sum_seq(rest)) + v == sum_seq(s) + v;
    assert sum_seq(s + [v]) == sum_seq(s) + v;
  }
}

lemma MinSeqAppend(s: seq<int>, v: int)
  requires |s| > 0
  ensures min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s)
{
  if |s| == 1 {
    var x := s[0];
    // s = [x]
    // min_seq([x] + [v]) == if v < x then v else x
    assert s == [x];
    assert min_seq(s) == x;
    assert min_seq(s + [v]) == (s + [v])[0] + 0 || true; // harmless to help unfolding
    // unfold min_seq for two-element sequence
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == [v];
    // min_seq([x, v]) == if x <= v then x else v
    if x <= v {
      assert min_seq(s + [v]) == x;
      assert (if v < min_seq(s) then v else min_seq(s)) == (if v < x then v else x);
      // since x <= v, v < x is false, so RHS == x
      assert (if v < x then v else x) == x;
      assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
    } else {
      // x > v
      assert min_seq(s + [v]) == v;
      if v < x {
        assert (if v < min_seq(s) then v else min_seq(s)) == v;
      } else {
        assert (if v < min_seq(s) then v else min_seq(s)) == x;
      }
      assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
    }
  } else {
    var x := s[0];
    var rest := s[1..];
    MinSeqAppend(rest, v);
    // Unfold min_seq(s + [v])
    // (s + [v])[0] == x
    // (s + [v])[1..] == rest + [v]
    assert (s + [v])[0] == x;
    assert (s + [v])[1..] == rest + [v];
    assert min_seq(s + [v]) == if x <= min_seq(rest + [v]) then x else min_seq(rest + [v]);
    // By inductive hypothesis min_seq(rest + [v]) == if v < min_seq(rest) then v else min_seq(rest)
    var restMin := min_seq(rest);
    var restMinApp := min_seq(rest + [v]);
    assert restMinApp == (if v < restMin then v else restMin);
    // Now consider cases on relation of x and restMinApp vs restMin to show desired equality
    if v < (if x <= restMin then x else restMin) {
      // v < min_seq(s)
      // Need to show min_seq(s + [v]) == v
      // From above, min_seq(s + [v]) == if x <= restMinApp then x else restMinApp
      if x <= restMinApp {
        // then min_seq(s + [v]) == x
        // but v < min_seq(s) and min_seq(s) == if x <= restMin then x else restMin
        // In this subcase we must have contradiction or x == v conditions; handle uniformly by chaining:
        // We can reason from restMinApp == if v < restMin then v else restMin
        // If x <= restMinApp and v < (if x <= restMin then x else restMin), it's possible only if v < x and restMinApp == v, so min_seq(s + [v]) == x or v; handle by direct case analysis below.
        // Do direct case-splitting on whether v < restMin
        if v < restMin {
          // restMinApp == v, so x <= restMinApp implies x <= v contradicts v < x; hence cannot happen
          reveal; // no-op to stress solver
        }
      }
    }
    // Simpler approach: show equality holds by expanding both sides and using IH; do case on whether v < restMin
    if v < restMin {
      // restMinApp == v
      // then min_seq(s + [v]) == if x <= v then x else v
      if x <= v {
        // min_seq(s + [v]) == x
        // min_seq(s) == if x <= restMin then x else restMin
        // since v < restMin and x <= v implies x <= restMin, so min_seq(s) == x
        assert min_seq(s + [v]) == x;
        assert (if v < min_seq(s) then v else min_seq(s)) == (if v < x then v else x);
        // since x <= v, v < x is false, RHS == x
        assert (if v < x then v else x) == x;
        assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
      } else {
        // x > v
        // min_seq(s + [v]) == v
        // min_seq(s) == if x <= restMin then x else restMin
        // since v < restMin, restMin >= v+1 possibly; but x > v doesn't decide relation to restMin. However:
        // If x <= restMin then min_seq(s) == x (> v), so RHS == v.
        // Else min_seq(s) == restMin (>= v+1), so RHS == v.
        assert min_seq(s + [v]) == v;
        assert (if v < min_seq(s) then v else min_seq(s)) == v;
        assert min_seq(s + [v]) == if v < min_seq(s) then v else min_seq(s);
      }
    } else {
      // v >= restMin, so restMinApp == restMin
      // then min_seq(s + [v]) == if x <= restMin then x else restMin == min_seq(s)
      assert restMinApp == restMin;
      assert min_seq(s + [v]) == (if x <= restMin then x else restMin);
      assert (if v < min_seq(s) then v else min_seq(s)) == (if v < (if x <= restMin then x else restMin) then v else (if x <= restMin then x else restMin));
      // Since restMinApp == restMin and min_seq(s) == (if x <= restMin then x else restMin), and v >= restMin,
      // v < min_seq(s) is false if min_seq(s) == restMin, and if min_seq(s) == x then v < x might be false/true but consistency holds.
      // In any case, both sides equal min_seq(s) when v >= restMin, so:
      assert min_seq(s + [v]) == min_seq(s);
      assert min_seq(s + [v]) == (if v < min_seq(s) then v else min_seq(s));
    }
  }
}

lemma SumIndicatorsEqualsCount(a: seq<int>, n: int)
  requires 0 <= n <= |a|
  ensures sum_seq(seq(n, k requires 0 <= k < n => if a[k] < 0 then 1 else 0)) == |set k | 0 <= k < n && a[k] < 0|
{
  if n == 0 {
    // both sides are 0
  } else {
    SumIndicatorsEqualsCount(a, n-1);
    var flag := if a[n-1] < 0 then 1 else 0;
    // apply SumSeqAppend to get sum relation
    SumSeqAppend(seq(n-1, k requires 0 <= k < n-1 => if a[k] < 0 then 1 else 0), flag);
    // reason about set cardinality growth
    if a[n-1] < 0 {
      // the set for length n equals previous set union {n-1} and n-1 not in previous set
      assert |set k | 0 <= k < n && a[k] < 0| == |set k |
// </vc-code>

