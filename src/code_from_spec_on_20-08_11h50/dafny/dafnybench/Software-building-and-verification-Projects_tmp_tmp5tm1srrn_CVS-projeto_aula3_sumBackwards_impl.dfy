// The `sum` function is already defined recursively as:
// - `sum(0) = 0`
// - `sum(n) = n + sum(n-1)` for `n > 0`
//
// So `sum(n)` computes `0 + 1 + 2 + ... + n`.
//
// I need to implement `sumBackwards` to compute this sum iteratively. I'll use a loop that goes from `n` down to 1, accumulating the sum.

// <vc-spec>
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
lemma sumProperty(k: nat)
  ensures sum(k) == k * (k + 1) / 2
{
  if k == 0 {
    // sum(0) == 0 and 0 * 1 / 2 == 0
  } else {
    sumProperty(k - 1);
    // sum(k) == k + sum(k-1) == k + (k-1)*k/2 == (2k + (k-1)*k)/2 == k*(k+1)/2
  }
}

lemma sumIncrement(n: nat, i: nat)
  requires 0 < i <= n
  ensures sum(n) - sum(i) + i == sum(n) - sum(i-1)
{
  // sum(i) = i + sum(i-1)
  // so sum(n) - sum(i) + i = sum(n) - (i + sum(i-1)) + i = sum(n) - sum(i-1)
  assert sum(i) == i + sum(i-1);
}
// </vc-helpers>

method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := n;
  
  while i > 0
    invariant 0 <= i <= n
    invariant r == sum(n) - sum(i)
    decreases i
  {
    sumIncrement(n, i);
    r := r + i;
    i := i - 1;
  }
}
// </vc-code>