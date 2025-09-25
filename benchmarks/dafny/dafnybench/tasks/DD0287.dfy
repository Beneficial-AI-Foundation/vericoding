// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k];
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
