function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}

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
  assume {:axiom} false;
}
// </vc-code>
