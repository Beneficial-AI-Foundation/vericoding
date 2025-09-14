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
lemma SumProperty(n: nat)
  ensures sum(n) == n * (n + 1) / 2
{
  if n == 0 {
    assert sum(0) == 0;
    assert 0 * 1 / 2 == 0;
  } else {
    SumProperty(n - 1);
    assert sum(n) == n + sum(n - 1);
    assert sum(n - 1) == (n - 1) * n / 2;
    assert sum(n) == n + (n - 1) * n / 2;
    assert sum(n) == (2 * n + (n - 1) * n) / 2;
    assert sum(n) == (2 * n + n * n - n) / 2;
    assert sum(n) == (n + n * n) / 2;
    assert sum(n) == n * (1 + n) / 2;
    assert sum(n) == n * (n + 1) / 2;
  }
}
// </vc-helpers>

// <vc-spec>
method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == i * (i + 1) / 2
  {
    i := i + 1;
    r := r + i;
  }
  SumProperty(n);
}
// </vc-code>

