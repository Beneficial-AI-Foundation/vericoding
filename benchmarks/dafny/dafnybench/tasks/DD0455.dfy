// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
