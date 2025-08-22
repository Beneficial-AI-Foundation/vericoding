//IMPL SmallestMissingNumber
method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
{
    v := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= v
        /* code modified by LLM (iteration 3): ensures all values less than v are in s */
        invariant forall k :: 0 <= k < v ==> k in s
        /* code modified by LLM (iteration 3): maintains relationship between v and current position */
        invariant i < |s| ==> v <= s[i]
        /* code modified by LLM (iteration 3): ensures v has not been seen in processed elements */
        invariant forall j :: 0 <= j < i ==> s[j] < v
    {
        if s[i] == v {
            /* code modified by LLM (iteration 3): when we find v, increment it */
            v := v + 1;
        } else if s[i] > v {
            /* code modified by LLM (iteration 3): when s[i] > v, we can stop since v is missing */
            break;
        }
        i := i + 1;
    }
}