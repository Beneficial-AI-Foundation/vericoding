

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
    var i := 0;
    while i < |s| / 2
        invariant 0 <= i <= |s| / 2
        invariant count == |set k | 0 <= k < i && s[k] != s[|s| - 1 - k]|
    {
        if s[i] != s[|s| - 1 - i] {
            count := count + 1;
        }
        i := i + 1;
    }
    return count;
}
// </vc-code>

