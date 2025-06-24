// ATOM 

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
    
    /* code modified by LLM (iteration 1): strengthened loop invariants and added helper assertions */
    while i < n && j < m
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant forall k :: 0 <= k < i ==> v[k] in w[..m]
        invariant i < n ==> forall k :: 0 <= k < j ==> w[k] < v[i]
        invariant i < n && j > 0 ==> w[j-1] < v[i]
    {
        if v[i] == w[j] {
            /* code modified by LLM (iteration 1): added assertion to help verification */
            assert v[i] in w[..m];
            i := i + 1;
            j := j + 1;
        } else if v[i] < w[j] {
            /* code modified by LLM (iteration 1): added lemma call and assertions for the not-found case */
            assert forall k :: 0 <= k < j ==> w[k] < v[i];
            assert j < m && w[j] > v[i];
            assert strictSorted(w[..]);
            assert forall k :: j <= k < m ==> w[j] <= w[k];
            assert forall k :: j < k < m ==> w[j] < w[k];
            assert forall k :: 0 <= k < m ==> w[k] != v[i];
            assert v[i] !in w[..m];
            b := false;
            return;
        } else {
            // v[i] > w[j], so advance j
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): added assertions for final case analysis */
    if i == n {
        assert forall k :: 0 <= k < n ==> v[k] in w[..m];
        b := true;
    } else {
        // i < n && j == m
        assert j == m;
        assert i < n;
        assert forall k :: 0 <= k < j ==> w[k] < v[i];
        assert forall k :: 0 <= k < m ==> w[k] < v[i];
        assert v[i] !in w[..m];
        assert !(forall k :: 0 <= k < n ==> v[k] in w[..m]);
        b := false;
    }
}