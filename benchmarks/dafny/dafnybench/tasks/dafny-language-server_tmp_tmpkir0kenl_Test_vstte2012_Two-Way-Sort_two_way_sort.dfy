// <vc-preamble>
function multisets<T>(s: seq<T>): multiset<T>
{
    if |s| == 0 then multiset{} 
    else multiset{s[0]} + multiset(s[1..])
}

method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
