//IMPL
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{
  more := x + y;
  less := x - y;
}

//IMPL
method Max(a: int, b: int) returns (c: int)
  ensures a <= c && b <= c
  ensures a == c || b == c
{
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}

method Testing() {
  var x := Max(3,15);
}

//IMPL
function max(a: int, b: int): int
{
  if a >= b then a else b
}

method Testing'() {
}

function abs(x: int): int
{
  if x < 0 then -x else x
}

//IMPL
method Abs(x: int) returns (y: int)
  ensures y == abs(x)
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}

method m(n: nat)
{
  var i := 0;
  while i != n
    /* code modified by LLM (iteration 1): added loop invariants and decreases clause for termination */
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
}

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

//IMPL
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := -1;
  var i := 0;
  while i < a.Length
    /* code modified by LLM (iteration 1): added loop invariants to prove postconditions */
    invariant 0 <= i <= a.Length
    invariant index == -1 || (0 <= index < i && a[index] == key)
    invariant index == -1 ==> forall k :: 0 <= k < i ==> a[k] != key
  {
    if a[i] == key {
      index := i;
      return;
    }
    i := i + 1;
  }
}

//IMPL
method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1 
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  i := 0;
  var j := 1;
  while j < a.Length
    /* code modified by LLM (iteration 1): added loop invariants to prove postconditions */
    invariant 1 <= j <= a.Length
    invariant 0 <= i < a.Length
    invariant forall k :: 0 <= k < j ==> a[k] <= a[i]
  {
    if a[j] > a[i] {
      i := j;
    }
    j := j + 1;
  }
}

predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

predicate sorted'(a: array?<int>) // Change the type
  reads a
{
  forall j, k :: a != null && 0 <= j < k < a.Length ==> a[j] <= a[k]
}