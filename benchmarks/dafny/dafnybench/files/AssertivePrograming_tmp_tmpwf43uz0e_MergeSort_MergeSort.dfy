// <vc-preamble>
predicate Sorted(q: seq<int>) {
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){
    (i <= |a1|) && (i <= |a2|) && (i+mid <= |a|) &&
    (a1[..i] == a[..i]) && (a2[..i] == a[mid..(i+mid)])
}

method Merge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
    modifies b
{
  assume{:axiom} false;
}

ghost predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    ((i+j > 0 && i < |c|) ==> (b[j + i - 1] <= c[i])) &&
    ((i+j > 0 && j < |d|) ==> (b[j + i - 1] <= d[j])) &&
    Sorted(b[..i+j])
    }

ghost predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MergeSort(a: array<int>) returns (b: array<int>)
    ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
    decreases a.Length
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
