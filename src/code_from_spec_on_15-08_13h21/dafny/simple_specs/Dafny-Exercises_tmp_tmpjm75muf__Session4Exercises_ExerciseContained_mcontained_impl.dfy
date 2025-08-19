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
    
    var i := 0; // pointer for v;
    var j := 0; // pointer for w;
    
    while i < n && j < m
        invariant 0 <= i <= n && 0 <= j <= m
        invariant forall k :: 0 <= k < i ==> v[k] in w[..m]
        invariant i < n ==> forall k :: 0 <= k < j ==> w[k] < v[i]
        /* code modified by LLM (iteration 1): added invariant to handle case when we exhaust w array */
        invariant j == m && i < n ==> !(forall k:: 0<= k< n ==> v[k] in w[..m])
    {
        if v[i] == w[j] {
            i := i + 1;
            j := j + 1;
        } else if v[i] > w[j] {
            j := j + 1;
        } else {
            // v[i] < w[j], but we've already checked all elements in w smaller than w[j]
            // Since w is strictly sorted, v[i] cannot be in w[..m]
            b := false;
            return;
        }
    }
    
    /* code modified by LLM (iteration 1): added explicit reasoning for the final assignment */
    // If we've checked all n elements from v, then all are contained in w
    // If we've exhausted w before checking all elements in v, then not all are contained
    if i == n {
        // All elements have been found
        b := true;
    } else {
        // We must have j == m and i < n, meaning we exhausted w without finding all elements
        b := false;
    }
}