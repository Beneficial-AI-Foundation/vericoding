// ATOM 

predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

// IMPL 

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
    
    var i := 0; // index for v
    var j := 0; // index for w
    
    while i < n && j < m
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant forall k :: 0 <= k < i ==> v[k] in w[..m]
        /* code modified by LLM (iteration 1): Added invariant to ensure all elements in v[0..i] are less than w[j] when they should be */
        invariant i > 0 && j < m ==> v[i-1] < w[j]
        /* code modified by LLM (iteration 1): Added invariant to track that all unmatched elements in w[0..j] are smaller than current v[i] */
        invariant i < n && j > 0 ==> w[j-1] < v[i]
    {
        if v[i] == w[j] {
            i := i + 1;
            j := j + 1;
        } else if v[i] < w[j] {
            /* code modified by LLM (iteration 1): Added lemma-style assertions to prove v[i] cannot be found */
            assert strictSorted(w[..]);
            assert forall l :: j <= l < m ==> w[j] <= w[l];
            assert forall l :: 0 <= l < j ==> w[l] < v[i];
            assert v[i] !in w[..m];
            b := false;
            return;
        } else {
            // v[i] > w[j], advance j
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Fixed final logic with proper case analysis */
    if i == n {
        b := true;
    } else {
        // i < n and j == m, which means v[i] cannot be in w[..m]
        assert j == m;
        assert i < n;
        /* code modified by LLM (iteration 1): Added assertion to prove v[i] is not in w[..m] */
        assert strictSorted(v[..]);
        assert forall k :: 0 <= k < i ==> v[k] < v[i];
        assert forall k :: 0 <= k < i ==> v[k] in w[..m];
        assert v[i] > w[m-1]; // This follows from the loop termination condition
        assert v[i] !in w[..m];
        b := false;
    }
}