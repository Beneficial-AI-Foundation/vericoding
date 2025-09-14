function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification

// <vc-helpers>
function fib(n: nat): nat
  decreases n
{
  if n == 0 then 1
  else if n == 1 then 1
  else fib(n-1) + fib(n-2)
}

lemma FibIsStairs(n: nat)
  ensures fib(n) == Stairs(n)
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    FibIsStairs(n-1);
    FibIsStairs(n-2);
  }
}
// </vc-helpers>

// <vc-spec>
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
// </vc-spec>
// <vc-code>
{
  FibIsStairs(n); // Prove that fib(n) is equivalent to Stairs(n)
  if n == 0 {
    r := 1;
  } else if n == 1 {
    r := 1;
  } else {
    var a: nat := 1; // Represents fib(i-2)
    var b: nat := 1; // Represents fib(i-1)
    var i: nat := 2;
    while i <= n
      invariant i <= n + 1
      invariant a == fib(i - 2)
      invariant b == fib(i - 1)
      decreases n - i
    {
      var next_b := a + b;
      a := b;
      b := next_b;
      i := i + 1;
    }
    r := b;
  }
}
// </vc-code>

