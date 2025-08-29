function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma FibSum(n: nat)
  ensures fib(n) + fib(n + 1) == fib(n + 2)
  decreases n
{
  if n == 0 {
    calc {
      fib(0) + fib(1);
      0 + 1;
      1;
      fib(2);
    }
  } else {
    calc {
      fib(n) + fib(n + 1);
      fib(n) + (fib(n) + fib(n - 1));
      { FibSum(n - 1); }
      fib(n) + fib(n + 1 - 1) + fib(n - 1);
      fib(n + 2);
    }
  }
}
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
    return 0;
  } else if n == 1 {
    return 1;
  }
  
  var prev := 0;
  var curr := 1;
  var i := 1;
  
  while i < n
    invariant 0 <= i <= n
    invariant prev == fib(i - 1)
    invariant curr == fib(i)
    decreases n - i
  {
    var next := prev + curr;
    prev := curr;
    curr := next;
    i := i + 1;
  }
  
  result := curr;
}
// </vc-code>
