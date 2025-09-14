

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
  var m := n;
  odd := 0;
  even := 0;
  while m > 0
    invariant m >= 0
    invariant odd + odd_count(m) == odd_count(n)
    invariant even + even_count(m) == even_count(n)
    decreases m
  {
    var d := m % 10;
    odd := odd + (d % 2);
    even := even + (1 - d % 2);
    m := m / 10;
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