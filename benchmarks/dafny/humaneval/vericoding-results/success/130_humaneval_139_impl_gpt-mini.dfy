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
/* helper modified by LLM (iteration 2): factorial positivity */
lemma FactorialPositive(n: int)
  requires n >= 0
  ensures factorial_func(n) > 0
  decreases n
{
  if n == 0 {
    assert factorial_func(0) == 1;
    assert factorial_func(0) > 0;
  } else {
    FactorialPositive(n - 1);
    assert factorial_func(n) == n * factorial_func(n - 1);
    assert factorial_func(n - 1) > 0;
    assert n > 0;
    assert factorial_func(n) > 0;
  }
}

/* helper modified by LLM (iteration 2): unfold special factorial */
lemma SpecialUnfold(k: int)
  requires k >= 1
  ensures special_factorial_func(k) == special_factorial_func(k - 1) * factorial_func(k)
{
  assert special_factorial_func(k) == special_factorial_func(k - 1) * factorial_func(k);
}

/* helper modified by LLM (iteration 2): special factorial positivity */
lemma SpecialPositive(n: int)
  requires n >= 0
  ensures special_factorial_func(n) > 0
  decreases n
{
  if n == 0 {
    assert special_factorial_func(0) == 1;
    assert special_factorial_func(0) > 0;
  } else {
    SpecialPositive(n - 1);
    FactorialPositive(n);
    assert special_factorial_func(n) == special_factorial_func(n - 1) * factorial_func(n);
    assert special_factorial_func(n - 1) > 0;
    assert factorial_func(n) > 0;
    assert special_factorial_func(n) > 0;
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
  /* code modified by LLM (iteration 2): compute special factorial by multiplying factorials */
  result := 1;
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant result == special_factorial_func(j - 1)
    invariant result > 0
  {
    var f := factorial(j);
    SpecialUnfold(j);
    result := result * f;
    j := j + 1;
  }
}

// </vc-code>
