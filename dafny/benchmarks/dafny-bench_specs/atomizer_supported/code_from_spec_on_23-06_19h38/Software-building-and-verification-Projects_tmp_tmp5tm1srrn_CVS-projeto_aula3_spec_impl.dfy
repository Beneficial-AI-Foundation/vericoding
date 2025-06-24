// ATOM 
function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}

//IMPL 
method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
{
  if n == 0 {
    r := 1;
  } else if n == 1 {
    r := 1;
  } else {
    var r1 := Fib(n-1);
    var r2 := Fib(n-2);
    r := r1 + r2;
  }
}

// 2.
// ATOM 
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

// ATOM 
function add(l : List<int>) : int {
  match l
  case Nil => 0
  case Cons(x,xs) => x + add(xs)
}

//IMPL 
method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
{
  match l
  case Nil => r := 0;
  case Cons(x, xs) => 
    var tail_sum := addImp(xs);
    r := x + tail_sum;
}

// 3.
//IMPL 
method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
  max := arr[0];
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j: int :: 0 <= j < i ==> arr[j] <= max
    invariant exists x::0 <= x < i && arr[x] == max
  {
    if arr[i] > max {
      max := arr[i];
    }
    i := i + 1;
  }
}

// 5.
//IMPL 
method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
  max := arr[arr.Length - 1];
  var i := arr.Length - 2;
  while i >= 0
    invariant -1 <= i < arr.Length - 1
    invariant forall j: int :: i < j < arr.Length ==> arr[j] <= max
    invariant exists x::i < x < arr.Length && arr[x] == max
  {
    if arr[i] > max {
      max := arr[i];
    }
    i := i - 1;
  }
}

// 6
// ATOM 
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}

//IMPL 
method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{
  r := 0;
  var i := n;
  while i > 0
    invariant 0 <= i <= n
    invariant r == sum(n) - sum(i)
  {
    r := r + i;
    i := i - 1;
  }
}