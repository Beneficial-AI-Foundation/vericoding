// <vc-preamble>
predicate ValidInput(n: int, m: int)
{
  n >= 1 && n <= 100000000 && m >= 1 && m <= 100000000
}

function power_of_two(n: int): int
  requires n >= 0
  ensures power_of_two(n) > 0
{
  if n == 0 then 1 else 2 * power_of_two(n - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result == m % power_of_two(n)
  ensures 0 <= result < power_of_two(n)
// </vc-spec>
// <vc-code>
{
  var power := power_of_two(n);
  result := m % power;
}
// </vc-code>
