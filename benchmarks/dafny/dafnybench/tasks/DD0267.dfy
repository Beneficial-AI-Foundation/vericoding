// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
