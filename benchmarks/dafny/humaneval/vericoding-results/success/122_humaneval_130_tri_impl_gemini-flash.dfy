// <vc-preamble>
function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add a helper to compute tribonacci values that satisfies the `decreases` clause of `tri`. */
function Trib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 3
  else if n == 2 then (1 + 2 / 2)
  else Trib(n - 1) + Trib(n - 2) + Trib(n - 3)
}
// </vc-helpers>

// <vc-spec>
method Tribonacci(n: nat) returns (result: seq<nat>)

  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri(i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced `new seq<nat>(size, k => 0)` with `new `T`[size]` for array initialization to fix compilation errors. */
{
  var tribonacciValues: array<nat>;
  tribonacciValues := new nat[n + 1];

  var i: nat := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> tribonacciValues[k] == tri(k)
  {
    tribonacciValues[i] := tri(i);
    i := i + 1;
  }

  result := tribonacciValues[..];
}
// </vc-code>
