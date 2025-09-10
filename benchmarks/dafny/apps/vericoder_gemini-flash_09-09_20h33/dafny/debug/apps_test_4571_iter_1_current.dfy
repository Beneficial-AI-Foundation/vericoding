predicate ValidInput(n: int, m: int) {
  1 <= n <= 100 && 1 <= m <= n && m <= 5
}

function power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1 else base * power(base, exp - 1)
}

function ExpectedTime(n: int, m: int): int
  requires ValidInput(n, m)
{
  (1900 * m + 100 * (n - m)) * power(2, m)
}

// <vc-helpers>
function power_iter(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1 else base * power_iter(base, exp - 1)
}

lemma power_is_power_iter(base: int, exp: int)
  requires exp >= 0
  ensures power(base, exp) == power_iter(base, exp)
  decreases exp
{
  if exp == 0 {
  } else {
    power_is_power_iter(base, exp - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result == ExpectedTime(n, m)
// </vc-spec>
// <vc-code>
{
  var time := (1900 * m + 100 * (n - m));
  var pow2_m := 1;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant pow2_m == power_iter(2, i)
  {
    pow2_m := pow2_m * 2;
    i := i + 1;
  }
  
  // Prove that power_iter(2, m) is equal to power(2, m)
  power_is_power_iter(2, m);

  result := time * pow2_m;
}
// </vc-code>

