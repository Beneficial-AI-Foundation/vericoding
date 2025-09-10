

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  ghost var seen: set<int> := {};
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|;
    invariant seen == (set j | 0 <= j < i && s[j] == x);
    invariant count == |seen|
  {
    seen := (set j | 0 <= j < i+1 && s[j] == x);
    count := |seen|;
    i := i + 1;
  }
}
// </vc-code>

