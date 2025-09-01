

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
  var m: nat := n;
  var ev: nat := 0;
  var od: nat := 0;
  while m > 0
    invariant even_count(n) == ev + even_count(m)
    invariant odd_count(n) == od + odd_count(m)
    invariant m <= n
    decreases m
  {
    assert 0 <= m % 2 < 2;
    assert even_count(m) == even_count(m / 10) + (1 - m % 2);
    assert odd_count(m) == odd_count(m / 10) + m % 2;
    ev := ev + (1 - m % 2);
    od := od + m % 2;
    m := m / 10;
  }
  assert m == 0;
  assert even_count(0) == 0;
  assert odd_count(0) == 0;
  even := ev;
  odd := od;
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