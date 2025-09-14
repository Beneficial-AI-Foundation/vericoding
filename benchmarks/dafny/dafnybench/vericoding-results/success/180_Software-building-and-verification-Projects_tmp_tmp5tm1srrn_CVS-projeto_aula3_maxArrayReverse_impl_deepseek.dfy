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
lemma maxZero(arr: array<int>, i: int, n: int)
  requires 0 <= i <= n <= arr.Length
  requires forall k: int :: 0 <= k < i ==> arr[k] <= 0
  ensures forall k: int :: 0 <= k < i ==> arr[k] <= 0
{
}

lemma maxLemma(arr: array<int>, i: int, m: int, n: int)
  requires 0 <= i <= n <= arr.Length
  requires forall k: int :: 0 <= k < i ==> arr[k] <= m
  requires exists k: int :: 0 <= k < i && arr[k] == m
  ensures forall k: int :: 0 <= k < i ==> arr[k] <= m
  ensures exists k: int :: 0 <= k < i && arr[k] == m
{
}

lemma maxPreservation(arr: array<int>, i: int, max: int)
  requires 0 <= i < arr.Length
  requires forall k: int :: 0 <= k < i ==> arr[k] <= max
  requires exists k: int :: 0 <= k < i && arr[k] == max
  ensures forall k: int :: 0 <= k < i+1 ==> arr[k] <= (if arr[i] > max then arr[i] else max)
  ensures exists k: int :: 0 <= k < i+1 && arr[k] == (if arr[i] > max then arr[i] else max)
{
  if arr[i] > max {
    assert forall k: int :: 0 <= k < i ==> arr[k] <= arr[i];
    assert arr[i] == arr[i];
  } else {
    assert forall k: int :: 0 <= k < i ==> arr[k] <= max;
    assert exists k: int :: 0 <= k < i && arr[k] == max;
  }
}
// </vc-helpers>

// <vc-spec>
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
    invariant forall k: int :: 0 <= k < i ==> arr[k] <= max
    invariant exists k: int :: 0 <= k < i && arr[k] == max
  {
    if arr[i] > max {
      max := arr[i];
      assert forall k: int :: 0 <= k < i ==> arr[k] <= max;
      assert exists k: int :: 0 <= k < i+1 && arr[k] == max;
    } else {
      assert forall k: int :: 0 <= k < i+1 ==> arr[k] <= max;
      assert exists k: int :: 0 <= k < i && arr[k] == max;
    }
    i := i + 1;
  }
  assert i == arr.Length;
}
// </vc-code>

