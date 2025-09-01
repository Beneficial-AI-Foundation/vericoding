

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
  c := |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|;
}
// </vc-code>

