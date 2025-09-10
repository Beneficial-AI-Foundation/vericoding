function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := 0;
  } else if n == 1 {
    result := 1;
  } else {
    var prev := 0;
    var curr := 1;
    var i := 2;
    while i <= n
      invariant 2 <= i <= n + 1
      invariant prev == fib(i - 2)
      invariant curr == fib(i - 1)
    {
      var temp := prev + curr;
      prev := curr;
      curr := temp;
      i := i + 1;
    }
    result := curr;
  }
}
// </vc-code>

