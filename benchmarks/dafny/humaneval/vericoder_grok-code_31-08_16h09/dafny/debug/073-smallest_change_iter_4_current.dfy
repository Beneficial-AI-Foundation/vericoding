

// <vc-helpers>
// No changes needed
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
// </vc-spec>
// <vc-code>
var count := 0;
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant count == |set j: int | 0 <= j < i && {:trigger s[j], s[|s| - 1 - j]} s[j] != s[|s| - 1 - j]|
  {
    if s[i] != s[|s| - 1 - i] {
      count := count + 1;
    }
    i := i + 1;
  }
  c := count;
// </vc-code>

