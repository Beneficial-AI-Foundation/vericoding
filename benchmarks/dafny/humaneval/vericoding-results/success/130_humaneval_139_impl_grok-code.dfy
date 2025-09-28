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
/* helper modified by LLM (iteration 3): added lemmas to prove positivity */

lemma FactorialPositive(m: int)
  requires m >= 0
  ensures factorial_func(m) > 0
{
  if m > 0 {
    FactorialPositive(m - 1);
  }
}

lemma SpecialFactorialPositive(n: int)
  requires n >= 0
  ensures special_factorial_func(n) > 0
{
  if n == 0 {
  } else {
    FactorialPositive(n);
    SpecialFactorialPositive(n - 1);
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
  /* code modified by LLM (iteration 3): added lemma invocation to prove result >0 */
  SpecialFactorialPositive(n);
  if n <= 0 {
    return 1;
  }
  result := 1;
  var fact := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant fact == factorial_func(i - 1)
    invariant result == special_factorial_func(i - 1)
  {
    fact := fact * i;
    result := result * fact;
    i := i + 1;
  }
}
// </vc-code>
