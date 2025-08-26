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

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != key
  {
    if a[i] == key {
      index := i;
      return;
    }
    i := i + 1;
  }
  index := -1;
}
// </vc-code>

predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}