// SPEC
// RUN: /print:log.bpl

method ArrayMap<A>(f: int -> A, a: array<A>)
 requires a != null
 requires forall j :: 0 <= j < a.Length ==> f.requires(j)
 requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j)
 modifies a
 ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j)
{
}


/*method GenericSort<A>(cmp: (A, A) -> bool, a: array<A>)
 requires a != null
 requires forall x, y :: a !in cmp.reads(x, y)
 requires forall x, y :: cmp.requires(x, y)
 modifies a
 ensures forall x, y :: cmp.requires(x, y)
 ensures forall x, y :: 0 <= x < y < a.Length ==> cmp(a[x], a[y])
{
}
