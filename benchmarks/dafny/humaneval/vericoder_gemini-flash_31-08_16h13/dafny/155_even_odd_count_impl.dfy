

// <vc-helpers>
function odd_count_spec(n: nat): nat {
  if n == 0 then 0
  else odd_count_spec(n / 10) + n % 2
}

function even_count_spec(n: nat): nat
{
  if n == 0 then 0
  else even_count_spec(n / 10) + (1 - n % 2)
}

function DigitCount(n: nat): nat
{
  if n == 0 then 0
  else 1 + DigitCount(n / 10)
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
  var e_count := 0;
  var o_count := 0;
  var temp_n := n;

  while temp_n > 0
    invariant e_count + even_count_spec(temp_n) == even_count_spec(n)
    invariant o_count + odd_count_spec(temp_n) == odd_count_spec(n)
    decreases temp_n
  {
    var digit := temp_n % 10;
    if digit % 2 == 0 {
      e_count := e_count + 1;
    } else {
      o_count := o_count + 1;
    }
    temp_n := temp_n / 10;
  }
  return e_count, o_count;
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