predicate strictSorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

// <vc-helpers>
predicate containedIn(v: array<int>, n: int, w: array<int>, m: int)
    reads v, w
{
    0 <= n <= v.Length && 0 <= m <= w.Length &&
    forall k :: 0 <= k < n ==> contains(w[..m], v[k])
}

predicate contains(s: seq<int>, e: int) {
    exists i :: 0 <= i < |s| && s[i] == e
}
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
    var i := 0;
    var j := 0;
    while i < n && j < m
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant forall k :: 0 <= k < i ==> exists l :: 0 <= l < j && w[l] == v[k]
        invariant i < n && j > 0 ==> v[i] > w[j-1]
    {
        if v[i] == w[j] {
            i := i + 1;
            j := j + 1;
        } else if v[i] < w[j] {
            return false;
        } else {
            j := j + 1;
        }
    }
    return i == n;
}
// </vc-code>

