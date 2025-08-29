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
lemma ThreeDistinctImpliesHappy(s: string, i: int)
    requires 0 < i < |s| - 1
    requires ThreeDistinct(s, i)
    ensures (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
{
}
// </vc-helpers>

// <vc-spec>
method IsHappy(s: string) returns (happy : bool)
    // post-conditions-start
    ensures happy <==> Happy(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
method IsHappy(s: string) returns (happy: bool)
    ensures happy <==> Happy(s)
{
    if |s| < 3 {
        return false;
    }
    
    happy := true;
    for i := 1 to |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant happy ==> forall k :: 1 <= k < i ==> ThreeDistinct(s, k)
    {
        if i < |s| - 1 && (s[i - 1] == s[i] || s[i] == s[i + 1] || s[i - 1] == s[i + 1]) {
            happy := false;
        }
    }
    if happy {
        assert forall k :: 1 <= k < |s| - 1 ==> ThreeDistinct(s, k);
    }
    return happy;
}
// </vc-code>
