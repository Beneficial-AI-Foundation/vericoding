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
  if k==0 then cur_minus_3
  else if k==1 then cur_minus_2
  else if k==2 then cur_minus_1
  else if k==3 then cur
  else fib4_iter(k - 1, cur_minus_2, cur_minus_1, cur, cur + cur_minus_1 + cur_minus_2 + cur_minus_3)
}

lemma fib4_iter_equals_fib4_rec(k: nat, cur_minus_3: nat, cur_minus_2: nat, cur_minus_1: nat, cur: nat)
  requires (k == 0 ==> cur_minus_3 == fib4_rec(0))
  requires (k == 1 ==> cur_minus_2 == fib4_rec(1))
  requires (k == 2 ==> cur_minus_1 == fib4_rec(2))
  requires (k == 3 ==> cur == fib4_rec(3))
  requires k >= 4 ==>
           cur_minus_3 == fib4_rec(k - 4) &&
           cur_minus_2 == fib4_rec(k - 3) &&
           cur_minus_1 == fib4_rec(k - 2) &&
           cur == fib4_rec(k - 1)
  ensures fib4_iter(k, cur_minus_3, cur_minus_2, cur_minus_1, cur) == fib4_rec(k)
  decreases k
{
  if k == 0 {
  } else if k == 1 {
  } else if k == 2 {
  } else if k == 3 {
  } else {
    fib4_iter_equals_fib4_rec(k - 1, cur_minus_2, cur_minus_1, cur, cur + cur_minus_1 + cur_minus_2 + cur_minus_3);
  }
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
  if n == 0 || n == 1 || n == 2 {
    result := 0;
  } else if n == 3 {
    result := 1;
  } else {
    var a: nat := 0;  // Corresponds to fib4_rec(i-4)
    var b: nat := 0;  // Corresponds to fib4_rec(i-3)
    var c: nat := 0;  // Corresponds to fib4_rec(i-2)
    var d: nat := 1;  // Corresponds to fib4_rec(i-1)

    var i: nat := 4; // i corresponds to the current fib4_rec index we are computing, starting from 4
    while i <= n
      invariant i >= 4
      invariant d == fib4_rec(i - 1)
      invariant c == fib4_rec(i - 2)
      invariant b == fib4_rec(i - 3)
      invariant a == fib4_rec(i - 4)
      decreases n - i
    {
      var next_fib: nat := d + c + b + a;
      a := b;
      b := c;
      c := d;
      d := next_fib;
      i := i + 1;
    }
    result := d;
  }
}
// </vc-code>

