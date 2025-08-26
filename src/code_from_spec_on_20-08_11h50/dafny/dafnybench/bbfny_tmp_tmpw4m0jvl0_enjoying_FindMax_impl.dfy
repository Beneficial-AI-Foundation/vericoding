function max(a: int, b: int): int
{
  if a > b then a else b
}
method Testing'() {
  assert max(1,2) == 2;
  assert forall a,b : int :: max (a,b) == a || max (a,b) == b;
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

// <vc-helpers>
// </vc-helpers>

method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1 
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
// </vc-spec>
// <vc-code>
{
  i := 0;
  var j := 1;
  while j < a.Length
    invariant 0 <= i < a.Length
    invariant 1 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[k] <= a[i]
  {
    if a[j] > a[i] {
      i := j;
    }
    j := j + 1;
  }
}
// </vc-code>

predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}