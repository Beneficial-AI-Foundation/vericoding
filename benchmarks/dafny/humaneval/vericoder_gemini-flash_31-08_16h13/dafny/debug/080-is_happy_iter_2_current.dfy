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
function IsHappy_helper(s: string) : bool
  reads s
  decreases |s|
{
  if |s| < 3 then
    true
  else if |s| == 3 then
    ThreeDistinct(s, 1)
  else
    && ThreeDistinct(s, 1) // Check the first requirement
    && (forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i)) // Check the general requirement
}
// </vc-helpers>

// <vc-spec>
method IsHappy(s: string) returns (happy : bool)
    // post-conditions-start
    ensures happy <==> Happy(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  happy := Happy(s);
}
// </vc-code>

