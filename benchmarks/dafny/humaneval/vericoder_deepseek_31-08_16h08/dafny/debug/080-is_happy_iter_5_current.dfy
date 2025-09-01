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
    ensures i >= |s| - 1 || s[i] != s[i+1]
    decreases |s| - i
{
    if i < |s| - 1 {
        if 0 < i && i < |s| - 1 {
            assert ThreeDistinct(s, i);
            assert s[i] != s[i+1];
        }
        if i + 1 < |s| {
            ThreeDistinctLemma(s, i+1);
        }
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
        if i >= |s| - 1 {
            break;
        }
        if !ThreeDistinct(s, i) {
            happy := false;
            return;
        }
        i := i + 1;
    }
    
    assert i == |s| - 1 || i == |s|;
}
// </vc-code>

