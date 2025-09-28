// <vc-preamble>

function factorial_func(num: int): int
    requires num >= 0
{
    if num <= 1 then 1 else num * factorial_func(num - 1)
}

function special_factorial_func(n: int): int
    requires n >= 0
{
    if n <= 0 then 1
    else special_factorial_func(n - 1) * factorial_func(n)
}
method factorial(num: int) returns (result: int)
    requires num >= 0
    ensures result == factorial_func(num)
    ensures result > 0
{
    if num <= 1 {
        return 1;
    }
    result := 1;
    var i := 2;
    while i <= num
        invariant 2 <= i <= num + 1
        invariant result == factorial_func(i - 1)
        invariant result > 0
    {
        result := result * i;
        i := i + 1;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to prove factorial_func returns positive values */
lemma factorial_positive(n: int)
    requires n >= 0
    ensures factorial_func(n) >= 1
{
    if n == 0 || n == 1 {
        // factorial_func(n) = 1, which is >=1
    } else {
        // n>=2
        factorial_positive(n-1);
        // Now we know factorial_func(n-1) >= 1, and n>=2, so n * factorial_func(n-1) >= 2 * 1 = 2 >=1.
    }
}
// </vc-helpers>

// <vc-spec>
method special_factorial(n: int) returns (result: int)
    requires n >= 0
    ensures result == special_factorial_func(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added explicit call to factorial_positive lemma in loop */
  if n == 0 {
    result := 1;
  } else {
    var sf := 1;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n+1
      invariant sf == special_factorial_func(i-1)
      invariant sf > 0
    {
      factorial_positive(i);
      sf := sf * factorial_func(i);
      i := i + 1;
    }
    result := sf;
  }
}
// </vc-code>
