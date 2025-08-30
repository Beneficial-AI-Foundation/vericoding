// SPEC
method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
 requires a != null && a.Length > 0
 requires forall x, y :: cmp.requires(x, y)
 requires forall x, y :: cmp(x, y) || cmp(y, x)
 requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z)

 ensures forall x :: 0 <= x < a.Length ==>
  // uncommenting the following line causes the program to verify
  // assume cmp.requires(a[x], max);
  cmp(a[x], max)
{
}
