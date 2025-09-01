

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
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set k | 0 <= k < i && s[k] == x)|
  {
    if s[i] == x {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>

