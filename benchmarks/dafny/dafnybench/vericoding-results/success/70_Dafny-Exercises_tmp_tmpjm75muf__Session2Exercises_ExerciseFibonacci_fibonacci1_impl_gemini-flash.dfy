function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma fib_add(a: nat, b: nat)
  requires a >= 1
  ensures fib(a + b) == fib(a - 1) * fib(b) + fib(a) * fib(b + 1)
  decreases b
{
  if b == 0 {
    // fib(a) == fib(a-1)*fib(0) + fib(a)*fib(1)
    // fib(a) == fib(a-1)*0 + fib(a)*1
  } else if b == 1 {
    // fib(a+1) == fib(a-1)*fib(1) + fib(a)*fib(2)
    // fib(a+1) == fib(a-1) + fib(a)
  } else {
    fib_add(a, b - 1);
    fib_add(a, b - 2);
  }
}
// </vc-helpers>

// <vc-spec>
method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    f := 0;
  } else if n == 1 {
    f := 1;
  } else {
    var a: nat := 0;
    var b: nat := 1;
    var i: nat := 2;
    while i <= n
      invariant i <= n + 1
      invariant b == fib(i-1)
      invariant a == fib(i-2)
    {
      var temp := b;
      b := a + b;
      a := temp;
      i := i + 1;
    }
    f := b;
  }
}
// </vc-code>

