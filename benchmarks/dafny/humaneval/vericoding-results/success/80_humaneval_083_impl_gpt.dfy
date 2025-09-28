// <vc-preamble>

predicate ValidInput(n: int) {
  n >= 1
}

function power(base: int, exp: int): int
  requires exp >= 0
  ensures base >= 0 ==> power(base, exp) >= 0
  ensures base > 0 ==> power(base, exp) > 0
  decreases exp
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}

function CountStartsWith1(n: int): int
  requires n >= 1
  ensures CountStartsWith1(n) == power(10, n - 1)
{
  power(10, n - 1)
}

function CountEndsWith1(n: int): int
  requires n >= 1
  ensures n == 1 ==> CountEndsWith1(n) == 1
  ensures n >= 2 ==> CountEndsWith1(n) == 9 * power(10, n - 2)
{
  if n == 1 then 1
  else 9 * power(10, n - 2)
}

function CountStartsAndEndsWith1(n: int): int
  requires n >= 1
  ensures n == 1 ==> CountStartsAndEndsWith1(n) == 1
  ensures n == 2 ==> CountStartsAndEndsWith1(n) == 1
  ensures n >= 3 ==> CountStartsAndEndsWith1(n) == power(10, n - 2)
{
  if n <= 2 then 1
  else power(10, n - 2)
}
// </vc-preamble>

// <vc-helpers>
lemma mult_ge_left(k: int, a: int)
  requires a >= 0
  requires k >= 1
  ensures k * a >= a
{
}

lemma power_step_int(k: int)
  requires k >= 0
  ensures power(10, k + 1) == 10 * power(10, k)
{
}
// </vc-helpers>

// <vc-spec>
method starts_one_ends(n: int) returns (result: int)
  requires ValidInput(n)
  ensures result == CountStartsWith1(n) + CountEndsWith1(n) - CountStartsAndEndsWith1(n)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := CountStartsWith1(n) + CountEndsWith1(n) - CountStartsAndEndsWith1(n);
  if n >= 3 {
    assert CountStartsWith1(n) == power(10, n - 1);
    assert CountStartsAndEndsWith1(n) == power(10, n - 2);
    assert CountEndsWith1(n) == 9 * power(10, n - 2);
    assert n - 2 >= 0;
    assert power(10, n - 2) >= 0;
    power_step_int(n - 2);
    assert power(10, n - 1) == 10 * power(10, n - 2);
    mult_ge_left(10, power(10, n - 2));
    assert CountStartsWith1(n) >= CountStartsAndEndsWith1(n);
    assert CountEndsWith1(n) >= 0;
    assert result >= 0;
  } else if n == 2 {
    assert CountStartsAndEndsWith1(n) == 1;
    assert CountStartsWith1(n) == power(10, n - 1);
    assert CountEndsWith1(n) == 9 * power(10, n - 2);
    assert n - 1 >= 0;
    assert n - 2 >= 0;
    assert power(10, n - 2) >= 0;
    assert CountEndsWith1(n) >= 0;
    assert power(10, n - 1) > 0;
    assert CountStartsWith1(n) >= 1;
    assert result >= 0;
  } else {
    assert CountStartsAndEndsWith1(n) == 1;
    assert CountEndsWith1(n) == 1;
    assert CountStartsWith1(n) == power(10, n - 1);
    assert n - 1 >= 0;
    assert power(10, n - 1) > 0;
    assert CountStartsWith1(n) >= 1;
    assert result >= 0;
  }
}
// </vc-code>
