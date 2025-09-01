

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
  var j := 0;
  while j < |s|
    invariant 0 <= j <= |s|
    invariant count == |(set k | 0 <= k < j && s[k] == x)|
  {
    if s[j] == x {
      count := count + 1;
    }
    j := j + 1;
  }
}
// </vc-code>

