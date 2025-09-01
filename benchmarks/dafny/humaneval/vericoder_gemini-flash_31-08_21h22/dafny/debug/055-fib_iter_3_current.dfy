function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma fib_increases(n: nat)
  ensures fib(n) <= fib(n + 1)
{
  if n == 0 {
    assert fib(0) == 0;
    assert fib(1) == 1;
    calc {
      fib(0);
      0;
      1;
      fib(1);
    }
  } else if n == 1 {
    assert fib(1) == 1;
    assert fib(2) == fib(1) + fib(0) == 1 + 0 == 1;
    calc {
      fib(1);
      1;
      fib(2);
    }
  } else {
    fib_increases(n-1);
    fib_increases(n-2);
    calc {
      fib(n);
      fib(n-1) + fib(n-2);
      fib(n-1) + fib(n-1); // fib(n-2) <= fib(n-1)
      fib(n) + fib(n-1); // fib(n-1) <= fib(n)
      fib(n+1);
    }
  }
}

lemma fib_n_minus_one_plus_fib_n_minus_two(n: nat)
  requires n >= 2
  ensures fib(n) == fib(n - 1) + fib(n - 2)
{}
// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var a: nat := 0;
  var b: nat := 1;
  var i: nat := 0;

  if n == 0 {
    return 0;
  }
  if n == 1 {
    return 1;
  }

  while i < n - 1
    invariant i <= n - 1
    invariant a == fib(i)
    invariant b == fib(i + 1)
    decreases n - 1 - i
  {
    i := i + 1;
    var temp := b;
    b := a + b;
    a := temp;
  }
  return b;
}
// </vc-code>

