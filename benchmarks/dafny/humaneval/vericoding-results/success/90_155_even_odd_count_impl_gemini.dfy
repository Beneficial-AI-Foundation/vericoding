// <vc-preamble>
function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// </vc-preamble>

// <vc-helpers>
lemma CountProperties(k: nat)
  requires k > 0
  ensures even_count(k) == even_count(k/10) + (1 - (k%10)%2)
  ensures odd_count(k) == odd_count(k/10) + (k%10)%2
{
  assert k % 2 == (k % 10) % 2;
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(n: nat) returns (even: nat, odd: nat)

  requires n > 0

  ensures even == even_count(n)
  ensures odd == odd_count(n)
// </vc-spec>
// <vc-code>
{
  even := 0;
  odd := 0;
  var temp_n := n;
  while temp_n > 0
    invariant even_count(n) == even + even_count(temp_n)
    invariant odd_count(n) == odd + odd_count(temp_n)
  {
    var digit := temp_n % 10;
    if digit % 2 == 0 {
      even := even + 1;
    } else {
      odd := odd + 1;
    }
    temp_n := temp_n / 10;
  }
}
// </vc-code>
