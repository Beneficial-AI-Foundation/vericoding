

// <vc-helpers>
function even_count_iter(n: nat, accumulator_even: nat): nat
  decreases n
{
  if n == 0 then accumulator_even
  else even_count_iter(n / 10, accumulator_even + (1 - n % 2))
}

function odd_count_iter(n: nat, accumulator_odd: nat): nat
  decreases n
{
  if n == 0 then accumulator_odd
  else odd_count_iter(n / 10, accumulator_odd + n % 2)
}

lemma even_odd_count_sum_digits(n: nat)
  ensures even_count(n) + odd_count(n) == (if n == 0 then 0 else n_digits(n))
{
  if n > 0 {
    even_odd_count_sum_digits(n / 10);
  }
}

function n_digits(n: nat): nat {
  if n == 0 then 0
  else 1 + n_digits(n / 10)
}

lemma even_count_even_count_iter(n: nat, accumulator_even: nat)
  ensures even_count(n) + accumulator_even == even_count_iter(n, accumulator_even)
{
  if n == 0 {
  } else {
    even_count_even_count_iter(n / 10, accumulator_even + (1 - n % 2));
  }
}

lemma odd_count_odd_count_iter(n: nat, accumulator_odd: nat)
  ensures odd_count(n) + accumulator_odd == odd_count_iter(n, accumulator_odd)
{
  if n == 0 {
  } else {
    odd_count_odd_count_iter(n / 10, accumulator_odd + n % 2);
  }
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(n: nat) returns (even: nat, odd: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures even == even_count(n)
  ensures odd == odd_count(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var even_acc := 0;
  var odd_acc := 0;
  var temp_n := n;

  // Loop invariant:
  // 1. original_even_count == even_count(temp_n) + even_acc
  // 2. original_odd_count == odd_count(temp_n) + odd_acc
  // where original_even_count and original_odd_count are the final counts for n.
  // We can establish this by proving:
  // even_count(n) == even_count(temp_n) + even_acc
  // odd_count(n) == odd_count(temp_n) + odd_acc
  // for the loop.

  // Before the loop, temp_n is n, even_acc is 0, odd_acc is 0.
  // The invariant holds:
  // even_count(n) == even_count(n) + 0 (true)
  // odd_count(n) == odd_count(n) + 0 (true)
  
  while temp_n > 0
    invariant even_count(n) == even_count(temp_n) + even_acc
    invariant odd_count(n) == odd_count(temp_n) + odd_acc
    decreases temp_n
  {
    var digit := temp_n % 10;
    if digit % 2 == 0 {
      even_acc := even_acc + 1;
    } else {
      odd_acc := odd_acc + 1;
    }
    temp_n := temp_n / 10;
  }

  // After the loop, temp_n is 0.
  // From loop invariants:
  // even_count(n) == even_count(0) + even_acc
  // even_count(n) == 0 + even_acc
  // even_count(n) == even_acc
  // Similarly, odd_count(n) == odd_acc

  even := even_acc;
  odd := odd_acc;
}
// </vc-code>

function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
// pure-end
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// pure-end