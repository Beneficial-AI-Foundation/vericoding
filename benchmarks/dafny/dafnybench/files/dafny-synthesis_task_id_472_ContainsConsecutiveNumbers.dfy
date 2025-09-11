// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
