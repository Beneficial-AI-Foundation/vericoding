

// <vc-helpers>
lemma even_count_digit_lemma(n: nat, digit: nat)
  requires n > 0
  requires digit == n % 10
  ensures even_count(n) == even_count(n / 10) + (1 - digit % 2)
{
  // Recursive case: expand the definition of even_count
  assert even_count(n) == even_count(n / 10) + (1 - n % 2);
  assert digit == n % 10;
  assert 1 - digit % 2 == 1 - (n % 10) % 2;
  assert (n % 10) % 2 == n % 2; // Mathematical property
  assert 1 - digit % 2 == 1 - n % 2;
}

lemma odd_count_digit_lemma(n: nat, digit: nat)
  requires n > 0
  requires digit == n % 10
  ensures odd_count(n) == odd_count(n / 10) + digit % 2
{
  // Recursive case: expand the definition of odd_count
  assert odd_count(n) == odd_count(n / 10) + n % 2;
  assert digit == n % 10;
  assert digit % 2 == (n % 10) % 2;
  assert (n % 10) % 2 == n % 2; // Mathematical property
}

lemma even_count_invariant_step(n: nat, temp: nat, even: nat, digit: nat)
  requires temp > 0
  requires digit == temp % 10
  requires even + even_count(temp) == even_count(n)
  ensures (even + (1 - digit % 2)) + even_count(temp / 10) == even_count(n)
{
  even_count_digit_lemma(temp, digit);
}

lemma odd_count_invariant_step(n: nat, temp: nat, odd: nat, digit: nat)
  requires temp > 0
  requires digit == temp % 10
  requires odd + odd_count(temp) == odd_count(n)
  ensures (odd + digit % 2) + odd_count(temp / 10) == odd_count(n)
{
  odd_count_digit_lemma(temp, digit);
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
  even := 0;
  odd := 0;
  var temp := n;
  
  while temp > 0
    invariant even + even_count(temp) == even_count(n)
    invariant odd + odd_count(temp) == odd_count(n)
    decreases temp
  {
    var digit := temp % 10;
    if digit % 2 == 0 {
      even_count_invariant_step(n, temp, even, digit);
      even := even + 1;
    } else {
      odd_count_invariant_step(n, temp, odd, digit);
      odd := odd + 1;
    }
    temp := temp / 10;
  }
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