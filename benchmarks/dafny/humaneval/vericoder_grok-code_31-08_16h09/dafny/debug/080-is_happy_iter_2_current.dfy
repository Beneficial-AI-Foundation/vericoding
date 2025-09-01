function ThreeDistinct(s: string, i: int): bool
    requires 0 < i < |s| - 1
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}
function Happy(s: string) : bool
{
    |s| >= 3 &&
    forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsHappy(s: string) returns (happy : bool)
    // post-conditions-start
    ensures happy <==> Happy(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
if |s| < 3 {
  happy := false;
} else {
  happy := true;
  var i := 1;
  while i < |s| - 1
    invariant 1 <= i <= |s| - 1
    invariant happy <==> (|s| >= 3 && forall k :: 1 <= k < i ==> ThreeDistinct(s, k))
  {
    happy := happy && ThreeDistinct(s, i);
    i := i + 1;
  }
}
// </vc-code>

