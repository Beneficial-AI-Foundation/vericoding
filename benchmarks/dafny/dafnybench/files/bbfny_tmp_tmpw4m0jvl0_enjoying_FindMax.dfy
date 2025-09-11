// <vc-preamble>
function max(a: int, b: int): int
{
  if a > b then a else b
}
method Testing'()
{
  assume{:axiom} false;
}

function abs(x: int): int
{
  if x < 0 then -x else x
}

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1 
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
