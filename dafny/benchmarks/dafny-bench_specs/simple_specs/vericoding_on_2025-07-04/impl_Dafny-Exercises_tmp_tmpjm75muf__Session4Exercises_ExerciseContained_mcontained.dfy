//ATOM

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
    
    var i := 0; // index for v
    var j := 0; // index for w
    
    /* code modified by LLM (iteration 1): strengthened loop invariants to prove postcondition */
    while i < n && j < m
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant forall k :: 0 <= k < i ==> v[k] in w[..m]
        invariant i < n ==> forall k :: 0 <= k < j ==> w[k] < v[i]
        invariant i < n && j == m ==> v[i] !in w[..m]
    {
        if v[i] == w[j] {
            i := i + 1;
            j := j + 1;
        } else if v[i] < w[j] {
            // v[i] is not in w[..m] because arrays are strictly sorted
            /* code modified by LLM (iteration 1): added assertion to help prove v[i] not in w[..m] */
            assert forall k :: 0 <= k < j ==> w[k] < v[i];
            assert forall k :: j <= k < m ==> v[i] < w[j] <= w[k];
            assert v[i] !in w[..m];
            b := false;
            return;
        } else {
            // v[i] > w[j], advance j
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): added assertions to prove correctness of final result */
    if i == n {
        // All elements of v[..n] have been found in w[..m]
        assert forall k :: 0 <= k < n ==> v[k] in w[..m];
        b := true;
    } else {
        // i < n && j == m, so v[i] is not in w[..m]
        assert i < n && j == m;
        assert v[i] !in w[..m];
        b := false;
    }
}