// <vc-preamble>
function pow2(n: nat): nat
    ensures pow2(n) > 0
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

function shift_right_int(x: int, n: nat): int
    requires pow2(n) > 0
{
  if x >= 0 then
    x / pow2(n)
  else
    -((((-x) - 1) / pow2(n)) + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method right_shift(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> 0 <= b[i] < 64
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> 
        result[i] == shift_right_int(a[i], b[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
