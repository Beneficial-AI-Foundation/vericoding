// <vc-preamble>
function power(x: real, n: nat) : real {
    if n == 0 then 1.0 else x * power(x, n-1)
}
// </vc-preamble>

// <vc-helpers>
lemma PowerLemma(x: real, a: nat, b: nat)
  ensures power(x, a) * power(x, b) == power(x, a + b)
  decreases b
{
  if b > 0 {
    PowerLemma(x, a, b - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var half := powerDC(x, n / 2);
    PowerLemma(x, n / 2, n / 2);
    p := half * half;
  } else {
    var prev := powerDC(x, n - 1);
    p := x * prev;
  }
}
// </vc-code>
