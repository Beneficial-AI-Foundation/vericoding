function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma FibMonotonic(i: nat, j: nat)
  requires i <= j
  ensures fib(i) <= fib(j)
{
  if i == j {
  } else if i == 0 {
    FibNonNegative(j);
  } else if i == 1 {
    if j == 1 {
    } else {
      FibMonotonic(1, j - 1);
      FibMonotonic(0, j - 2);
    }
  } else {
    FibMonotonic(i - 1, j - 1);
    FibMonotonic(i - 2, j - 2);
  }
}

lemma FibNonNegative(n: nat)
  ensures fib(n) >= 0
{
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
    result := 0;
  } else if n == 1 {
    result := 1;
  } else {
    var a := 0;
    var b := 1;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == fib(i - 2)
      invariant b == fib(i - 1)
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    
    result := b;
  }
}
// </vc-code>
