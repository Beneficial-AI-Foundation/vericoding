

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  ghost var seen: set<int> := {};
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == set j | 0 <= j < i
    invariant count == |set j | j in seen && s[j]==x|
  {
    if s[i] == x {
      count := count + 1;
    }
    seen := seen + {i};
    i := i + 1;
  }
}
// </vc-code>

