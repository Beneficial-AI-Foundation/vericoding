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
    // fib(n-1) <= fib(n) and fib(n-2) <= fib(n)
    // We want to prove fib(n) <= fib(n+1)
    // fib(n) = fib(n-1) + fib(n-2)
    // fib(n+1) = fib(n) + fib(n-1)
    // We need fib(n-1) + fib(n-2) <= fib(n) + fib(n-1)
    // This simplifies to fib(n-2) <= fib(n) -- which is true by induction
    // We already have fib_increases(n-1) which gives fib(n-1) <= fib(n)
    fib_increases(n-1); // fib(n-1) <= fib(n)
    fib_increases(n-2); // fib(n-2) <= fib(n-1)
    calc {
      fib(n);
      fib(n-1) + fib(n-2);
      { assert fib(n-2) <= fib(n-1); }
      fib(n-1) + fib(n-1);
      { assert fib(n-1) > 0 ==> fib(n-1) + fib(n-1) >= fib(n-1);
        assert fib(n-1) <= fib(n); // from fib_increases(n-1)
      }
      fib(n) + fib(n-1);
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
    invariant i < n
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

