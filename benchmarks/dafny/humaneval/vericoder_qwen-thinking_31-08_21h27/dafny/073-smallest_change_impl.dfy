

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
  var c := 0;
  for i in 0 to (n / 2) {
    invariant c == |{ j | 0 <= j < i && s[j] != s[n - 1 - j] }|
    if s[i] != s[n - 1 - i] {
      c := c + 1;
    }
  }
  return c;
}
// </vc-code>

