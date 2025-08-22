//ATOM fib
function fib(n: nat): nat
{
  if n <= 1 then n else fib(n-2) + fib(n-1)
}

//ATOM Fib
method Fib(n: nat) returns (result: nat)
  ensures result == fib(n)
{
  if n <= 1 {
    result := n;
  } else {
    var a := Fib(n-2);
    var b := Fib(n-1);
    result := a + b;
  }
}

//ATOM List
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM add
function add(xs: List<int>, ys: List<int>): List<int>
{
  match xs
  case Nil => ys
  case Cons(h, t) => Cons(h, add(t, ys))
}

//ATOM addImp
method addImp(xs: List<int>, ys: List<int>) returns (result: List<int>)
  ensures result == add(xs, ys)
{
  match xs
  case Nil => result := ys;
  case Cons(h, t) => 
    var tailResult := addImp(t, ys);
    result := Cons(h, tailResult);
}

//ATOM maxArray
method maxArray(arr: array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x :: 0 <= x < arr.Length && arr[x] == max
{
  max := arr[0];
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j: int :: 0 <= j < i ==> arr[j] <= max
    invariant exists x :: 0 <= x < i && arr[x] == max
  {
    if arr[i] > max {
      max := arr[i];
    }
    i := i + 1;
  }
}

//IMPL maxArrayReverse
method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
  max := arr[arr.Length - 1];
  var i := arr.Length - 2;
  /* code modified by LLM (iteration 1): Fixed loop invariants to properly establish postconditions */
  while i >= 0
    invariant -1 <= i <= arr.Length - 2
    invariant forall j: int :: i < j < arr.Length ==> arr[j] <= max
    invariant exists x :: i < x < arr.Length && arr[x] == max
    invariant i < arr.Length - 1 ==> (forall j: int :: i < j < arr.Length ==> arr[j] <= max)
  {
    if arr[i] > max {
      max := arr[i];
    }
    i := i - 1;
  }
}

//ATOM sum
function sum(arr: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= arr.Length
  reads arr
{
  if start == end then 0
  else arr[start] + sum(arr, start + 1, end)
}

//ATOM sumBackwards
method sumBackwards(arr: array<int>) returns (total: int)
  ensures total == sum(arr, 0, arr.Length)
{
  total := 0;
  var i := arr.Length;
  while i > 0
    invariant 0 <= i <= arr.Length
    invariant total == sum(arr, i, arr.Length)
  {
    i := i - 1;
    total := total + arr[i];
  }
}