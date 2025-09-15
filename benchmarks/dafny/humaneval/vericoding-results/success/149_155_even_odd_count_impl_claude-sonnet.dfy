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
  var temp := n;
  while temp > 0
    invariant even + odd == even_count(n) - even_count(temp) + odd_count(n) - odd_count(temp)
    invariant even_count(n) == even + even_count(temp)
    invariant odd_count(n) == odd + odd_count(temp)
    decreases temp
  {
    if temp % 2 == 0 {
      even := even + 1;
    } else {
      odd := odd + 1;
    }
    temp := temp / 10;
  }
}
// </vc-code>
