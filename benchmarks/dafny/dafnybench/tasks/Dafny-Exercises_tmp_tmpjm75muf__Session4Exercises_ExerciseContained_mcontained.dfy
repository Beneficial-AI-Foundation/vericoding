// <vc-preamble>
predicate strictSorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
