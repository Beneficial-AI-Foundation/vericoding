

// <vc-helpers>

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
  var current := n;
  var even := 0;
  var odd := 0;

  while current != 0
    invariant even + even_count(current) == even_count(n)
    invariant odd + odd_count(current) == odd_count(n)
    decreases current
  {
    var digit := current % 10;
    if digit % 2 == 0 {
      even := even + 1;
    } else {
      odd := odd + 1;
    }
    current := current / 10;
  }

  return (even, odd);
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