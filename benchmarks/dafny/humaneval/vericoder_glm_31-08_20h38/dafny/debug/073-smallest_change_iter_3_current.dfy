

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
  var count := 0;
  for i := 0 to |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant count == |set j | 0 <= j < i && s[j] != s[|s| - 1 - j]|
  {
    if (s[i] != s[|s| - 1 - i]) then
      count := count + 1;
  }
  return count;
}
// </vc-code>

