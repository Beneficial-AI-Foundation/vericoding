function ThreeDistinct(s: string, i: int): bool
    requires 0 < i < |s| - 1
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}
// pure-end
function Happy(s: string) : bool
{
    |s| >= 3 &&
    forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i)
}
// pure-end
method IsHappy(s: string) returns (happy : bool)
    // post-conditions-start
    ensures happy <==> Happy(s)
    // post-conditions-end
    {
        // impl-start
        if |s| < 3 {
            return false;
        }

        var i := 1;
        while(i < |s| - 1)
            // invariants-start
            invariant 0 < i <= |s| - 1
            invariant forall j :: 0 < j < i ==> ThreeDistinct(s, j)
            // invariants-end
        {
            if !ThreeDistinct(s, i) {
                return false;
            }
            i := i + 1;
        }
        return true;
        // impl-end
    }
