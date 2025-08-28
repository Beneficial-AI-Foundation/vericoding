// shenanigans going through the dafny tutorial




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

// <vc-helpers>
lemma MaxProperty(a: array<int>, i: int)
  requires a.Length >= 1
  requires 0 <= i < a.Length
  requires forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  // This lemma is trivially true as it restates the requirement as the ensured condition.
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1 
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindMaxImpl(a: array<int>) returns (i: int)
  requires a.Length >= 1
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  i := 0;
  var currentMax := a[0];
  var index := 0;
  
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant 0 <= i < a.Length
    invariant forall k :: 0 <= k < index ==> a[k] <= currentMax
    invariant currentMax == a[i]
  {
    if a[index] > currentMax {
      currentMax := a[index];
      i := index;
    }
    index := index + 1;
  }
}
// </vc-code>
