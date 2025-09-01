

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
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && s[j] == x)|
  {
    if s[i] == x {
      count := count + 1;
    }
  }
}
// </vc-code>

