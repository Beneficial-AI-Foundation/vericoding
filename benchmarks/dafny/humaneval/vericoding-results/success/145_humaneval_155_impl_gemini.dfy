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
lemma lemma_sum_of_counts_equals_total_digits(n: nat)
    requires n >= 0
    ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n)
    decreases n
{
    if n >= 10 {
        lemma_sum_of_counts_equals_total_digits(n / 10);
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
  var n := abs_value(num);
  var temp_n := n;
  even_count := 0;
  odd_count := 0;

  lemma_sum_of_counts_equals_total_digits(n);

  while temp_n >= 10
    decreases temp_n
    invariant n == abs_value(num)
    invariant temp_n >= 0
    invariant count_even_digits(n) == even_count + count_even_digits(temp_n)
    invariant count_odd_digits(n) == odd_count + count_odd_digits(temp_n)
  {
    var digit := temp_n % 10;
    if is_even_digit(digit) {
      even_count := even_count + 1;
    } else {
      odd_count := odd_count + 1;
    }
    temp_n := temp_n / 10;
  }

  if is_even_digit(temp_n) {
    even_count := even_count + 1;
  } else {
    odd_count := odd_count + 1;
  }
}
// </vc-code>
