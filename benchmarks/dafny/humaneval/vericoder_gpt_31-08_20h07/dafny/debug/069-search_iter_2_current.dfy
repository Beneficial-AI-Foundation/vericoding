

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
  var i := 0;
  count := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && s[j] == x)|
    decreases |s| - i
  {
    if s[i] == x {
      assert i !in (set j | 0 <= j < i && s[j] == x);
      assert |(set j | 0 <= j < i && s[j] == x) + {i}| == |(set j | 0 <= j < i && s[j] == x)| + 1;
      assert (set j | 0 <= j < i + 1 && s[j] == x) == (set j | 0 <= j < i && s[j] == x) + {i};
      count := count + 1;
    } else {
      assert (set j | 0 <= j < i + 1 && s[j] == x) == (set j | 0 <= j < i && s[j] == x);
    }
    i := i + 1;
  }
  assert i == |s|;
}
// </vc-code>

