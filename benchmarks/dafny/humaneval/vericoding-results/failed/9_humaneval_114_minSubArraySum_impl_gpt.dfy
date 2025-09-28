// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define prefix sum utilities and telescoping relation between Sum and Prefix */
function Prefix(a: seq<int>, k: int): int
  requires 0 <= k <= |a|
{
  Sum(a, 0, k)
}

lemma PrefixStep(a: seq<int>, k: int)
  requires 0 <= k <= |a|
  ensures Prefix(a, k) == (if k == 0 then 0 else Prefix(a, k - 1) + a[k - 1])
{
  if k == 0 {
  } else {
    assert Prefix(a, k) == Sum(a, 0, k);
    assert Prefix(a, k - 1) == Sum(a, 0, k - 1);
    assert Sum(a, 0, k) == Sum(a, 0, k - 1) + a[k - 1];
  }
}

lemma SumPrefix(a: seq<int>, p: int, q: int)
  requires 0 <= p <= q <= |a|
  ensures Sum(a, p, q) == Prefix(a, q) - Prefix(a, p)
  decreases q - p
{
  if p == q {
    assert Sum(a, p, q) == 0;
    assert Prefix(a, q) - Prefix(a, p) == 0;
  } else {
    SumPrefix(a, p, q - 1);
    PrefixStep(a, q);
    assert Sum(a, p, q) == Sum(a, p, q - 1) + a[q - 1];
    assert Sum(a, p, q - 1) + a[q - 1] == (Prefix(a, q - 1) - Prefix(a, p)) + a[q - 1];
    assert (Prefix(a, q - 1) - Prefix(a, p)) + a[q - 1] == (Prefix(a, q - 1) + a[q - 1]) - Prefix(a, p);
    assert (Prefix(a, q - 1) + a[q - 1]) - Prefix(a, p) == Prefix(a, q) - Prefix(a, p);
  }
}
// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)

  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): maintain prefix maxima and prove invariant extension with explicit case analysis */
  var n := |a|;
  var j := 0;
  var pref := Prefix(a, 0);
  var maxPref := pref;
  var maxIdx := 0;
  var best := 0;
  var bestStart := 0;
  var bestEnd := 0;

  while j <= n
    invariant 0 <= j <= n + 1
    invariant 0 <= maxIdx <= n
    invariant maxIdx <= j
    invariant maxPref == Prefix(a, maxIdx)
    invariant j <= n ==> pref == Prefix(a, j)
    invariant forall i :: 0 <= i <= j && i <= n ==> Prefix(a, i) <= maxPref
    invariant 0 <= bestStart <= bestEnd <= n
    invariant Sum(a, bestStart, bestEnd) == best
    invariant forall p, q :: 0 <= p <= q < j && q <= n ==> Sum(a, p, q) >= best
    decreases n - j + 1
  {
    var current := pref - maxPref;
    var oldBest := best;

    // Snapshot the previous invariant into a fact parametrized by oldBest
    assert forall p, q :: 0 <= p <= q < j && q <= n ==> Sum(a, p, q) >= oldBest by {
      forall p, q | 0 <= p <= q < j && q <= n {
        assert Sum(a, p, q) >= best;
        assert best == oldBest;
      }
    }

    // Consider extending with subarrays ending at j
    if current < best {
      best := current;
      bestStart := maxIdx;
      bestEnd := j;
      SumPrefix(a, bestStart, bestEnd);
      assert best == Prefix(a, bestEnd) - Prefix(a, bestStart);
      assert Sum(a, bestStart, bestEnd) == best;
    }

    // Relations between best, oldBest, and current
    assert oldBest >= best by {
      if current < oldBest {
        assert best == current;
        assert oldBest >= current;
      } else {
        assert best == oldBest;
      }
    };
    assert best <= current by {
      if current < oldBest {
        assert best == current;
      } else {
        assert best == oldBest;
        assert oldBest <= current;
      }
    };

    // Establish invariant for j+1
    assert forall p, q :: 0 <= p <= q < j + 1 && q <= n ==> Sum(a, p, q) >= best by {
      forall p, q | 0 <= p <= q < j + 1 && q <= n {
        if q < j {
          assert Sum(a, p, q) >= oldBest;
          assert oldBest >= best;
        } else {
          // q == j
          assert q == j;
          SumPrefix(a, p, j);
          assert 0 <= p <= j; // from guard
          assert j <= n;      // from loop condition
          // From invariant, Prefix(a, p) <= maxPref
          assert 0 <= p <= j && p <= n;
          assert Prefix(a, p) <= maxPref;
          assert Sum(a, p, j) == Prefix(a, j) - Prefix(a, p);
          assert Prefix(a, j) - Prefix(a, p) >= Prefix(a, j) - maxPref;
          assert Prefix(a, j) - maxPref == current;
          if current < oldBest {
            assert best == current;
          } else {
            assert best == oldBest;
            assert oldBest <= current;
          }
        }
      }
    };

    if j < n {
      PrefixStep(a, j + 1);
      assert Prefix(a, j + 1) == Prefix(a, j) + a[j];
      pref := pref + a[j];
      assert pref == Prefix(a, j + 1);

      if pref > maxPref {
        maxPref := pref;
        maxIdx := j + 1;
      } else {
        assert pref <= maxPref;
      }
    }

    j := j + 1;
  }

  s := best;
}
// </vc-code>
