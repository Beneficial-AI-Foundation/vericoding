// ATOM 
function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}


// SPEC 

method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
{
}


// 2.
// ATOM 

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)
// ATOM 

function add(l : List<int>) : int {
  match l
  case Nil => 0
  case Cons(x,xs) => x + add(xs)
}


// SPEC 

method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
{
}


// 3.
// SPEC 

// 3.
method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
}


// 5.
// SPEC 

// 5.
method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
}


// 6
// ATOM 

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}


// SPEC 

method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{
}


