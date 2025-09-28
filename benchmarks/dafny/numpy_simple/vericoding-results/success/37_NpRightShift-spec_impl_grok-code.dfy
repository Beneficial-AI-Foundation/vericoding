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
/* code modified by LLM (iteration 5): fixed loop bounds error by using while loop to handle n=0 case */
var n := a.Length;
result := new int[n];
var j := 0;
while j < n
  invariant 0 <= j <= n
  invariant forall k :: 0 <= k < j ==> result[k] == shift_right_int(a[k], b[k])
{
  result[j] := shift_right_int(a[j], b[j]);
  j := j + 1;
}
}
// </vc-code>
