// <vc-preamble>

predicate ValidInput(n: int) {
    n > 0
}

function fib_spec(n: int): int
    requires n > 0
{
    if n == 1 then 1
    else if n == 2 then 1
    else fib_spec(n-1) + fib_spec(n-2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fib(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == fib_spec(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := 1;
  } else if n == 2 {
    result := 1;
  } else {
    var prev2 := 1;
    var prev1 := 1;
    var i := 3;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant prev2 == fib_spec(i - 2)
      invariant prev1 == fib_spec(i - 1)
      invariant prev1 > 0 && prev2 > 0
    {
      var temp := prev1 + prev2;
      prev2 := prev1;
      prev1 := temp;
      i := i + 1;
    }
    result := prev1;
  }
}
// </vc-code>
