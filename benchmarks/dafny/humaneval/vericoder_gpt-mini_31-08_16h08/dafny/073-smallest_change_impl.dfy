

// <vc-helpers>
lemma CountSetInc(s: seq<int>, n: int, i: int)
  requires n == |s|
  requires 0 <= i < n / 2
  ensures |set k | 0 <= k < i + 1 && s[k] != s[n - 1 - k]| ==
          |set k | 0 <= k < i && s[k] != s[n - 1 - k]| + (if s[i] != s[n - 1 - i] then 1 else 0)
{
  if s[i] != s[n - 1 - i] {
    assert (set k | 0 <= k < i + 1 && s[k] != s[n - 1 - k]) ==
           (set k | 0 <= k < i && s[k] != s[n - 1 - k]) + {i};
    assert forall k :: k in (set k | 0 <= k < i && s[k] != s[n - 1 - k]) ==> k < i;
    assert !(i in (set k | 0 <= k < i && s[k] != s[n - 1 - k]));
    assert |(set k | 0 <= k < i && s[k] != s[n - 1 - k]) + {i}| ==
           |set k | 0 <= k < i && s[k] != s[n - 1 - k]| + 1;
  } else {
    assert (set k | 0 <= k < i + 1 && s[k] != s[n - 1 - k]) ==
           (set k | 0 <= k < i && s[k] != s[n - 1 - k]);
  }
}

lemma CountBound(s: seq<int>, n: int, i: int)
  requires n == |s|
  requires 0 <= i <= n / 2
  ensures |set k | 0 <= k < i && s[k] != s[n - 1 - k]| <= i
{
  if i == 0 {
    // empty set has size 0
  } else {
    // i > 0
    CountBound(s, n, i - 1);
    // use CountSetInc to relate sizes
    CountSetInc(s, n, i - 1);
    // let prev := |set k | 0 <= k < i - 1 && ...|
    // then current = prev + (if ... then 1 else 0) <= (i-1) + 1 = i
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
    // bound the current count by oldi
    CountBound(s, n, oldi);
    // relate sizes for the next i
    CountSetInc(s, n, oldi);
    i := oldi + 1;
    if neq {
      // from invariant and CountBound we get cnt <= oldi, hence cnt + 1 <= oldi + 1 <= n/2
      assert cnt <= oldi;
      cnt := cnt + 1;
    }
    assert cnt == |set k | 0 <= k < i && s[k] != s[n - 1 - k]|;
  }
  c := cnt;
}
// </vc-code>

