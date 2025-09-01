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
lemma ThreeDistinctLemma(s: string, i: int)
    requires 0 <= i < |s|
    requires forall j :: 0 < j < |s| - 1 ==> ThreeDistinct(s, j)
    ensures s[i] != s[i+1] || i >= |s| - 1
    decreases |s| - i
{
    if i < |s| - 1 && 0 < i {
        assert ThreeDistinct(s, i);
    }
    if i < |s| - 1 {
        ThreeDistinctLemma(s, i+1);
    }
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
    happy := true;
    
    while i < |s| - 1
        invariant 1 <= i <= |s|
        invariant happy <==> (forall j :: 0 < j < i ==> ThreeDistinct(s, j))
    {
        if !ThreeDistinct(s, i) {
            happy := false;
            return;
        }
        i := i + 1;
    }
    
    // After the loop, we need to ensure the invariant implies the postcondition
    // The loop invariant gives us: happy <==> (forall j :: 0 < j < i ==> ThreeDistinct(s, j))
    // When the loop exits, i = |s| - 1, so this becomes:
    // happy <==> (forall j :: 0 < j < |s| - 1 ==> ThreeDistinct(s, j))
    // Which is exactly the definition of Happy(s) when |s| >= 3
}
// </vc-code>

