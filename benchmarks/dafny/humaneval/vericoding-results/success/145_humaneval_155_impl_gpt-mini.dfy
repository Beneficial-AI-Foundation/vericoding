// <vc-preamble>

function abs_value(x: int): int
{
    if x < 0 then -x else x
}

function count_digits(n: nat): nat
    requires n >= 0
{
    if n < 10 then 1 else 1 + count_digits(n / 10)
}

function is_even_digit(d: nat): bool
    requires d < 10
{
    d % 2 == 0
}

function count_even_digits(n: nat): nat
    requires n >= 0
    decreases n
{
    if n < 10 then
        if is_even_digit(n) then 1 else 0
    else
        (if is_even_digit(n % 10) then 1 else 0) + count_even_digits(n / 10)
}

function count_odd_digits(n: nat): nat
    requires n >= 0
    decreases n
{
    if n < 10 then
        if !is_even_digit(n) then 1 else 0
    else
        (if !is_even_digit(n % 10) then 1 else 0) + count_odd_digits(n / 10)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): abs_value non-negativity */
lemma AbsValueNonNegative(x: int)
  ensures abs_value(x) >= 0
{
  if x < 0 {
    assert -x >= 0;
  } else {
    assert x >= 0;
  }
}

/* helper modified by LLM (iteration 2): proved counts sum equals digits */
lemma CountEvenOddSum(n: int)
  requires n >= 0
  ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n)
  decreases n
{
  if n < 10 {
    if is_even_digit(n) {
      assert count_even_digits(n) == 1;
      assert count_odd_digits(n) == 0;
      assert count_digits(n) == 1;
    } else {
      assert count_even_digits(n) == 0;
      assert count_odd_digits(n) == 1;
      assert count_digits(n) == 1;
    }
  } else {
    var last := n % 10;
    CountEvenOddSum(n / 10);
    assert count_even_digits(n) == (if is_even_digit(last) then 1 else 0) + count_even_digits(n / 10);
    assert count_odd_digits(n) == (if !is_even_digit(last) then 1 else 0) + count_odd_digits(n / 10);
    assert (if is_even_digit(last) then 1 else 0) + (if !is_even_digit(last) then 1 else 0) == 1;
    assert count_even_digits(n) + count_odd_digits(n) == 1 + (count_even_digits(n/10) + count_odd_digits(n/10));
    assert count_even_digits(n/10) + count_odd_digits(n/10) == count_digits(n/10);
    assert 1 + count_digits(n/10) == count_digits(n);
  }
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(num: int) returns (even_count: int, odd_count: int)
    ensures even_count >= 0 && odd_count >= 0
    ensures even_count + odd_count >= 1
    ensures var abs_num := abs_value(num);
            even_count == count_even_digits(abs_num) &&
            odd_count == count_odd_digits(abs_num)
    ensures even_count + odd_count == count_digits(abs_value(num))
    ensures num == 0 ==> (even_count == 1 && odd_count == 0)
    ensures abs_value(num) == abs_value(-num) ==> 
            (even_count == count_even_digits(abs_value(-num)) && 
             odd_count == count_odd_digits(abs_value(-num)))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute counts and invoke lemmas to prove sum property */
  var abs_num := abs_value(num);
  even_count := count_even_digits(abs_num);
  odd_count := count_odd_digits(abs_num);
  AbsValueNonNegative(num);
  CountEvenOddSum(abs_num);
}
// </vc-code>
