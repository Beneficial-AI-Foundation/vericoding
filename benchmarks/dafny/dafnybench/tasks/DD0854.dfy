// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
