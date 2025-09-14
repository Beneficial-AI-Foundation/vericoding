

// <vc-helpers>
lemma BitsShiftLemma(n: bv32, d: int)
  requires 0 <= d < 32
  ensures (n << d) | (n >> (32 - d)) == (n << d) | (n >> (32 - d))
{
}
// </vc-helpers>

// <vc-spec>
method RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
  result := (n << d) | (n >> (32 - d));
}
// </vc-code>

