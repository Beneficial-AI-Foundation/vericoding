function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
function fib4_rec_prev_terms(n: nat, a: nat, b: nat, c: nat, d: nat): nat
  decreases n
{
  if n == 0 then a
  else if n == 1 then b
  else if n == 2 then c
  else if n == 3 then d
  else fib4_rec_prev_terms(n - 1, b, c, d, a + b + c + d)
}

lemma fib4_rec_eq(n: nat, a: nat, b: nat, c: nat, d: nat)
  ensures fib4_rec_prev_terms(n, a, b, c, d) == 
          (if n == 0 then a 
           else if n == 1 then b 
           else if n == 2 then c 
           else if n == 3 then d 
           else fib4_rec(n + 4))
  decreases n
{
  if n > 3 {
    fib4_rec_eq(n - 1, b, c, d, a + b + c + d);
  }
}

lemma fib4_rec_helper(n: nat)
  ensures fib4_rec(n) == fib4_rec_prev_terms(n, 0, 0, 0, 1)
  decreases n
{
  if n == 0 {}
  else if n == 1 {}
  else if n == 2 {}
  else if n == 3 {}
  else if n > 3 {
    fib4_rec_helper(n - 1);
    fib4_rec_helper(n - 2);
    fib4_rec_helper(n - 3);
    fib4_rec_helper(n - 4);
    fib4_rec_eq(n - 4, 0, 0, 0, 1);
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
    var a := 0;  // F(0)
    var b := 0;  // F(1) 
    var c := 0;  // F(2)
    var d := 1;  // F(3)
    var i := 4;
    
    while i <= n
      invariant i >= 4 && i <= n + 1
      invariant a == fib4_rec(i - 4)
      invariant b == fib4_rec(i - 3)
      invariant c == fib4_rec(i - 2)
      invariant d == fib4_rec(i - 1)
    {
      var next := a + b + c + d;
      a := b;
      b := c;
      c := d;
      d := next;
      i := i + 1;
    }
    
    result := d;
  }
}
// </vc-code>

