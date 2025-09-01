function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
function fib4_iter(k: nat, cur_minus_3: nat, cur_minus_2: nat, cur_minus_1: nat, cur: nat): nat
  decreases k
{
  if k == 0 then cur_minus_3
  else if k == 1 then cur_minus_2
  else if k == 2 then cur_minus_1
  else if k == 3 then cur
  else fib4_iter(k-1, cur_minus_2, cur_minus_1, cur, cur + cur_minus_1 + cur_minus_2 + cur_minus_3)
}

lemma fib4_iter_equals_fib4_rec(k: nat, cur_minus_3: nat, cur_minus_2: nat, cur_minus_1: nat, cur: nat)
  requires k >= 3
  requires cur_minus_3 == fib4_rec(k - 3)
  requires cur_minus_2 == fib4_rec(k - 2)
  requires cur_minus_1 == fib4_rec(k - 1)
  requires cur == fib4_rec(k)
  ensures fib4_iter(k+1, cur_minus_2, cur_minus_1, cur, cur + cur_minus_1 + cur_minus_2 + cur_minus_3) == fib4_rec(k+1)
{
  // The postcondition of fib4_iter suggests a property that holds for each iteration.
  // We can use the definition of fib4_rec to show this equality.
  // fib4_rec(k+1) == fib4_rec(k) + fib4_rec(k-1) + fib4_rec(k-2) + fib4_rec(k-3)
  // By the preconditions, this is equal to cur + cur_minus_1 + cur_minus_2 + cur_minus_3.
}

lemma fib4_iter_matches_fib4_rec_general(n: nat)
  ensures (n >= 3 ==> fib4_iter(n, fib4_rec(n-3), fib4_rec(n-2), fib4_rec(n-1), fib4_rec(n)) == fib4_rec(n))
  ensures (n == 0 ==> fib4_iter(0,0,0,0,0) == fib4_rec(0))
  ensures (n == 1 ==> fib4_iter(1,0,0,0,0) == fib4_rec(1))
  ensures (n == 2 ==> fib4_iter(2,0,0,0,0) == fib4_rec(2))
  ensures (n == 3 ==> fib4_iter(3,0,0,0,1) == fib4_rec(3))
  // This lemma needs to be more general to show that the loop maintains the fib4_rec property.
{
  // For the base cases (n < 3), the value of fib4_rec is always 0.
  // fib4_rec(0) == 0
  // fib4_rec(1) == 0
  // fib4_rec(2) == 0
  // For n == 3, fib4_rec(3) == 1.
  // The fib4_iter in the loop initialization is effectively (k, 0, 0, 0, 1) when k goes from 3 up to n.
  // The `fib4_iter` function is defined such that it correctly computes `fib4_rec(k)` when given the previous 4 terms.
}
// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib4_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 || n == 2 then return 0
  else if n == 3 then return 1
  else
    var a: nat := 0; // fib4_rec(0)
    var b: nat := 0; // fib4_rec(1)
    var c: nat := 0; // fib4_rec(2)
    var d: nat := 1; // fib4_rec(3)
    var i: nat := 4;

    while i <= n
      invariant i <= n + 1
      invariant a == fib4_rec(i - 4)
      invariant b == fib4_rec(i - 3)
      invariant c == fib4_rec(i - 2)
      invariant d == fib4_rec(i - 1)
      decreases n - i
    {
      var next_d := d + c + b + a;
      a := b;
      b := c;
      c := d;
      d := next_d;
      i := i + 1;
    }
    return d;
}
// </vc-code>

