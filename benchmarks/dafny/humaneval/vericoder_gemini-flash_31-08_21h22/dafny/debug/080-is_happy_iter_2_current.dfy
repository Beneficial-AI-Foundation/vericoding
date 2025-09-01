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
// No helpers needed for this problem - the existing functions are sufficient.
// </vc-helpers>

// <vc-spec>
method IsHappy(s: string) returns (happy : bool)
    // post-conditions-start
    ensures happy <==> Happy(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |s| < 3 {
        happy := false;
    } else {
        var isCurrentlyHappy := true;
        for i := 1 to |s| - 2
            invariant 0 < i <= |s| - 1
            invariant isCurrentlyHappy ==> (forall k :: 0 < k < i ==> ThreeDistinct(s, k))
            invariant !isCurrentlyHappy ==> (exists k :: 0 < k < i && !ThreeDistinct(s, k))
            decreases |s| - i
        {
            if !ThreeDistinct(s, i) {
                isCurrentlyHappy := false;
            }
        }
        happy := isCurrentlyHappy;
    }
}
// </vc-code>

