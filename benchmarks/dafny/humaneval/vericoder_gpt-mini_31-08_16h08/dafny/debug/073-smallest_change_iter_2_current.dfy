

// <vc-helpers>
lemma CountSetInc(s: seq<int>, n: int, i: int)
  requires 0 <= i < n / 2
  ensures |set k | 0 <= k < i + 1 && s[k] != s[n - 1 - k]| ==
          |set k | 0 <= k < i && s[k] != s[n - 1 - k]| + (if s[i] != s[n - 1 - i] then 1 else 0)
{
  if s[i] != s[n - 1 - i] {
    // The set for i+1 is the previous set plus {i}
    assert (set k | 0 <= k < i + 1 && s[k] != s[n - 1 - k]) ==
           (set k | 0 <= k < i && s[k] != s[n - 1 - k]) + {i};
    // show i is not in the previous set (elements there are < i)
    assert forall k :: k in (set k | 0 <= k < i && s[k] != s[n - 1 - k]) ==> k < i;
    assert not (i in (set k | 0 <= k < i && s[k] != s[n - 1 - k]));
    // union with a singleton disjoint element increases cardinality by 1
    assert |(set k | 0 <= k < i && s[k] != s[n - 1 - k]) + {i}| ==
           |set k | 0 <= k < i && s[k] != s[n - 1 - k]| + 1;
  } else {
    // The set for i+1 equals the previous set
    assert (set k | 0 <= k < i + 1 && s[k] != s[n - 1 - k]) ==
           (set k | 0 <= k < i && s[k] != s[n - 1 - k]);
  }
}
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var i := 0;
  var cnt := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant 0 <= cnt <= n / 2
    invariant cnt == |set k | 0 <= k < i && s[k] != s[n - 1 - k]|
    decreases n / 2 - i
  {
    var oldi := i;
    var neq := s[oldi] != s[n - 1 - oldi];
    if neq {
      cnt := cnt + 1;
    }
    i := oldi + 1;
    CountSetInc(s, n, oldi);
    assert cnt == |set k | 0 <= k < i && s[k] != s[n - 1 - k]|;
  }
  c := cnt;
}
// </vc-code>

