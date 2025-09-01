

// <vc-helpers>

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
    if s[i] != s[n - 1 - i] {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  c := cnt;
}
// </vc-code>

