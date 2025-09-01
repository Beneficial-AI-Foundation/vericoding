

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
  var i := 0;
  ghost var seen: set<int> := {};
  ghost var matched: set<int> := {};
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == {0..i-1}
    invariant count == |matched|
    invariant matched <= seen
    invariant forall j :: j in matched ==> s[j] == x
    invariant forall j :: j in seen && s[j] == x ==> j in matched
  {
    if s[i] == x {
      count := count + 1;
      matched := matched + {i};
    }
    seen := seen + {i};
    i := i + 1;
  }
}
// </vc-code>

