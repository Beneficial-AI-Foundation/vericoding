predicate strictSorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]//exists j :: 0 <= j < m && v[k] == w[j]
// </vc-spec>
// <vc-code>
{
  b := forall k :: 0 <= k < n ==> v[k] in w[..m];
}
// </vc-code>

