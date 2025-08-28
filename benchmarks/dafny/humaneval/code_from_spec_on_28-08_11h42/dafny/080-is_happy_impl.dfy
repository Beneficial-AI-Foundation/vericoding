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
lemma ThreeDistinctCheck(s: string, i: int)
    requires 0 < i < |s| - 1
    ensures ThreeDistinct(s, i) <==> (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
{
}

lemma HappyEquivalence(s: string)
    ensures Happy(s) <==> (|s| >= 3 && forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i))
{
}

lemma AllThreeDistinctImpliesHappy(s: string)
    requires |s| >= 3
    requires forall j :: 0 < j < |s| - 1 ==> ThreeDistinct(s, j)
    ensures Happy(s)
{
}

lemma NotThreeDistinctImpliesNotHappy(s: string, k: int)
    requires |s| >= 3
    requires 0 < k < |s| - 1
    requires !ThreeDistinct(s, k)
    ensures !Happy(s)
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
{
    if |s| < 3 {
        happy := false;
        return;
    }
    
    var i := 1;
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant forall j :: 0 < j < i ==> ThreeDistinct(s, j)
    {
        if !(s[i - 1] != s[i] && s[i] != s[i + 1] && s[i - 1] != s[i + 1]) {
            NotThreeDistinctImpliesNotHappy(s, i);
            happy := false;
            return;
        }
        i := i + 1;
    }
    
    AllThreeDistinctImpliesHappy(s);
    happy := true;
}
// </vc-code>
