function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma fib_base0() ensures fib(0) == 0
{
  reveal fib(0);
}

lemma fib_base1() ensures fib(1) == 1
{
  reveal fib(1);
}

lemma fib_step(k: nat) ensures fib(k + 2) == fib(k + 1) + fib(k)
{
  reveal fib(k + 2);
}
// </vc-helpers>

// <vc-spec>
method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// <vc-code>
{
  var a: nat := 0;
  var b: nat := 1;
  var i: nat := 0;

  fib_base0();
  fib_base1();

  while i < n
    invariant i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
    decreases n - i
  {
    fib_step(i);
    var a0 := a;
    var b0 := b;
    a := b0;
    b := b0 + a0;
    i := i + 1;
  }
  f := a;
}
// </vc-code>

