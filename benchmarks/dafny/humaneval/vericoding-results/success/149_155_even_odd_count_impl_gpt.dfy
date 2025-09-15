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
lemma odd_count_unfold(m: nat)
  ensures odd_count(m) == (if m == 0 then 0 else odd_count(m / 10) + m % 2)
{
  if m == 0 {
  } else {
  }
}

lemma even_count_unfold(m: nat)
  ensures even_count(m) == (if m == 0 then 0 else even_count(m / 10) + (1 - m % 2))
{
  if m == 0 {
  } else {
  }
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
  var m: nat := n;
  even := 0;
  odd := 0;
  while m != 0
    invariant odd + odd_count(m) == odd_count(n)
    invariant even + even_count(m) == even_count(n)
    invariant odd >= 0 && even >= 0
    decreases m
  {
    odd_count_unfold(m);
    even_count_unfold(m);
    assert 0 <= m % 2 && m % 2 <= 1;
    assert 0 <= 1 - m % 2 && 1 - m % 2 <= 1;
    odd := odd + m % 2;
    even := even + (1 - m % 2);
    m := m / 10;
  }
  odd_count_unfold(0);
  even_count_unfold(0);
  assert odd_count(0) == 0;
  assert even_count(0) == 0;
}
// </vc-code>
