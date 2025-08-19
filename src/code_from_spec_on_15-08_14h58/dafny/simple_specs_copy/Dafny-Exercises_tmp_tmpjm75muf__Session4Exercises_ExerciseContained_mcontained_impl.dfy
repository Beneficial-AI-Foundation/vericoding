predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

//IMPL 

method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]//exists j :: 0 <= j < m && v[k] == w[j]
{
    if n == 0 {
        b := true;
        return;
    }
    
    var i := 0; // index for v;
    var j := 0; // index for w;
    
    while i < n && j < m
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant forall k :: 0 <= k < i ==> v[k] in w[..m]
        /* code modified by LLM (iteration 3): corrected invariant to track processed elements */
        invariant forall k :: 0 <= k < i ==> exists l :: 0 <= l < j && v[k] == w[l]
    {
        if v[i] == w[j] {
            i := i + 1;
            j := j + 1;
        } else if v[i] < w[j] {
            /* code modified by LLM (iteration 3): simplified proof using strict sorting */
            assert strictSorted(w[..]);
            assert forall l :: j <= l < m ==> w[j] <= w[l];
            assert forall l :: j < l < m ==> w[j] < w[l];
            assert v[i] < w[j];
            assert forall l :: j <= l < m ==> v[i] < w[l];
            assert forall l :: 0 <= l < j ==> w[l] < w[j];
            assert forall l :: 0 <= l < j ==> w[l] < v[i];
            assert v[i] !in w[..m];
            b := false;
            return;
        } else {
            // v[i] > w[j], advance j
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 3): fixed bounds checking and logic */
    if i < n {
        // We must have j == m (exhausted w but not v)
        assert j == m;
        assert v[i] !in w[..m];
        b := false;
        return;
    }
    
    // If we've processed all elements of v, they are all contained
    assert i == n;
    b := true;
}