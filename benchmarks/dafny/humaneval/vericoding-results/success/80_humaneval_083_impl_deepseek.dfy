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

  lemma StartsAndEndsWith1IncludedInBoth(n: int)
    requires n >= 1
    ensures CountStartsAndEndsWith1(n) <= CountStartsWith1(n)
    ensures CountStartsAndEndsWith1(n) <= CountEndsWith1(n)
  {
    if n == 1 {
    } else if n == 2 {
    } else {
    }
  }

  lemma ValidResult(n: int)
    requires n >= 1
    ensures CountStartsWith1(n) + CountEndsWith1(n) - CountStartsAndEndsWith1(n) >= 0
  {
    StartsAndEndsWith1IncludedInBoth(n);
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
  ValidResult(n);
  result := CountStartsWith1(n) + CountEndsWith1(n) - CountStartsAndEndsWith1(n);
}
// </vc-code>
