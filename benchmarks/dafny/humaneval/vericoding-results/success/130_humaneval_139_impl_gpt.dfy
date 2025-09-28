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
/* helper modified by LLM (iteration 2): provide unfolding lemma for special_factorial_func at n > 0 */
lemma special_factorial_step(n: int)
    requires n > 0
    ensures special_factorial_func(n) == special_factorial_func(n - 1) * factorial_func(n)
{
    assert n > 0;
    assert special_factorial_func(n) == special_factorial_func(n - 1) * factorial_func(n);
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
  /* code modified by LLM (iteration 2): fixed call syntax and implemented iterative computation using factorial and step lemma */
  if n <= 0 {
    return 1;
  }
  result := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == special_factorial_func(i - 1)
    invariant result > 0
  {
    var fi := factorial(i);
    assert fi > 0;
    var prod := result * fi;
    assert prod > 0;
    special_factorial_step(i);
    assert fi == factorial_func(i);
    assert prod == special_factorial_func(i);
    result := prod;
    i := i + 1;
  }
}
// </vc-code>
