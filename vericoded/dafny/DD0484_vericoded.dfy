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
lemma sumLemma(n: nat, k: nat)
  requires k <= n
  ensures sum(n) == sum(k) + (n - k) * (n + k + 1) / 2
  decreases n - k
{
  if k == n {
    assert sum(n) == sum(k) + 0;
  } else {
    sumLemma(n, k + 1);
    assert sum(k + 1) == (k + 1) + sum(k);
    assert sum(n) == sum(k + 1) + (n - k - 1) * (n + k + 2) / 2;
    assert sum(n) == (k + 1) + sum(k) + (n - k - 1) * (n + k + 2) / 2;
  }
}
// </vc-helpers>

// <vc-spec>
method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
// </vc-spec>
// <vc-code>
{
  var i := n;
  r := 0;
  
  while i > 0
    invariant 0 <= i <= n
    invariant r == sum(n) - sum(i)
  {
    r := r + i;
    i := i - 1;
  }
  
  assert i == 0;
  assert r == sum(n) - sum(0);
  assert sum(0) == 0;
}
// </vc-code>

