

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
  count := 0;
  var j := 0;
  ghost var theSet: set<int> := {};
  while j < |s|
    invariant 0 <= j <= |s|
    invariant theSet == (set k | 0 <= k < j && s[k] == x)
    invariant count == |theSet|
  {
    if s[j] == x {
      theSet := theSet + {j};
      count := count + 1;
    }
    j := j + 1;
  }
}
// </vc-code>

