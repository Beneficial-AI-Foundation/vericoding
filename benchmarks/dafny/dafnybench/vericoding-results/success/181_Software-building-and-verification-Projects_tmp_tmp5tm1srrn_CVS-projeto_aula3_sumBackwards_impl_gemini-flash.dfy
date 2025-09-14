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
function sum_of_nats(n: nat) : nat
{
  if (n == 0) then 0 else n + sum_of_nats(n-1)
}
lemma sum_is_sum_of_nats(n: nat)
  ensures sum(n) == sum_of_nats(n)
{
  if n == 0 {
    // Both are 0
  } else {
    calc {
      sum(n);
      n + sum(n-1);
      n + sum_of_nats(n-1); // by induction hypothesis
      sum_of_nats(n);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
// </vc-spec>
// <vc-code>
{
  var k := n;
  var r_sum := 0;
  ghost var initial_sum_of_nats_n := sum_of_nats(n);
  while k > 0
    invariant r_sum + sum_of_nats(k) == initial_sum_of_nats_n
    decreases k
  {
    r_sum := r_sum + k;
    k := k - 1;
  }
  // At this point, k is 0.
  // The invariant becomes: r_sum + sum_of_nats(0) == initial_sum_of_nats_n
  // Since sum_of_nats(0) is 0, we have: r_sum == initial_sum_of_nats_n
  // And by lemma: initial_sum_of_nats_n == sum(n)
  // Therefore: r_sum == sum(n)
  
  // Prove that sum_of_nats(n) is equal to sum(n)
  sum_is_sum_of_nats(n);

  return r_sum;
}
// </vc-code>

