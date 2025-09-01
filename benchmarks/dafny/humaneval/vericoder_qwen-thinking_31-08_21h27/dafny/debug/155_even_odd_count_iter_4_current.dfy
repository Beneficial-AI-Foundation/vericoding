

// <vc-helpers>
lemma EvenCountStep(current: nat, d: nat)
  requires current > 0
  requires d == current % 10
  ensures even_count(current) == even_count(current / 10) + (1 - (d % 2))
{}

lemma OddCountStep(current: nat, d: nat)
  requires current > 0
  requires d == current % 10
  ensures odd_count(current) == odd_count(current / 10) + (d % 2)
{}
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
var current := n;
  var even_acc := 0;
  var odd_acc := 0;
  while current > 0
    invariant even_acc + even_count(current) == even_count(n)
    invariant odd_acc + odd_count(current) == odd_count(n)
    decreases current
  {
    var digit := current % 10;
    if digit % 2 == 0 {
      even_acc := even_acc + 1;
    } else {
      odd_acc := odd_acc + 1;
    }
    current := current / 10;
  }
  even := even_acc;
  odd := odd_acc;
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