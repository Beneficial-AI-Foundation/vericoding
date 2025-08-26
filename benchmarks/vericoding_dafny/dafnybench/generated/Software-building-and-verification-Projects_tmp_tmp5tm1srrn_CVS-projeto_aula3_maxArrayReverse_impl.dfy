function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}


// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l : List<int>) : int {
  match l
  case Nil => 0
  case Cons(x,xs) => x + add(xs)
}


// 3.

// 5.

// <vc-helpers>
// </vc-helpers>

method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
// </vc-spec>
// <vc-code>
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
// </vc-code>

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}