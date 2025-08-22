//IMPL 
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    found := false;
    c := ' '; // default value
    
    var i := 0;
    while i < |s|
        /* code modified by LLM (iteration 2): Fixed outer loop invariant to correctly track checked pairs */
        invariant 0 <= i <= |s|
        invariant !found ==> (forall k, l :: 0 <= k < l < |s| && k < i ==> s[k] != s[l])
        invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
    {
        var j := i + 1;
        while j < |s|
            /* code modified by LLM (iteration 2): Fixed inner loop invariant to properly track current search */
            invariant i < j <= |s|
            invariant !found ==> (forall k :: i < k < j ==> s[i] != s[k])
            invariant !found ==> (forall k, l :: 0 <= k < l < |s| && k < i ==> s[k] != s[l])
            invariant found ==> exists p, q :: 0 <= p < q < |s| && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
        {
            if s[i] == s[j] {
                /* code modified by LLM (iteration 2): Added proper verification that this is the first repeated pair */
                assert 0 <= i < j < |s| && s[i] == s[j];
                assert forall k, l :: 0 <= k < l < |s| && k < i ==> s[k] != s[l];
                assert forall k :: i < k < j ==> s[i] != s[k];
                assert forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i;
                found := true;
                c := s[i];
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}