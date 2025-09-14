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

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
// </vc-spec>
// <vc-code>
{
  if arr.Length == 1 {
    max := arr[0];
  } else {
    max := arr[arr.Length - 1];
    var i := arr.Length - 2;
    while i >= 0
      decreases i
      invariant 0 <= i + 1 <= arr.Length
      invariant forall j :: i + 1 <= j < arr.Length ==> arr[j] <= max
      invariant exists j :: i + 1 <= j < arr.Length && arr[j] == max
    {
      if arr[i] > max {
        max := arr[i];
      }
      i := i - 1;
    }
  }
}
// </vc-code>

