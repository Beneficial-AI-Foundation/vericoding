

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
  even := 0;
  odd := 0;
  var num := n;
  
  while num > 0
    invariant even == even_count(n) - even_count(num)
    invariant odd == odd_count(n) - odd_count(num)
  {
    var digit := num % 10;
    if digit % 2 == 0 {
      even := even + 1;
    } else {
      odd := odd + 1;
    }
    num := num / 10;
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