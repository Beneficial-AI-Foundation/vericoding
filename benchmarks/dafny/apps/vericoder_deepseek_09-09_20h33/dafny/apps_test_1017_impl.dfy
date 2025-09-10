predicate ValidInput(n: int) {
    n >= 1
}

function MaxDistributions(n: int): int
    requires ValidInput(n)
{
    if n % 3 == 0 then 2 * (n / 3) else 2 * (n / 3) + 1
}

// <vc-helpers>
lemma ModThreeCases(n: int)
  requires n >= 1
  ensures n % 3 == 0 || n % 3 == 1 || n % 3 == 2
{
}

lemma DivModRelation(n: int, d: int)
  requires d != 0
  ensures n == (n / d) * d + n % d
{
}

lemma MaxDistributionsDefinition(n: int)
  requires ValidInput(n)
  ensures MaxDistributions(n) == (if n % 3 == 0 then 2 * (n / 3) else 2 * (n / 3) + 1)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures result == MaxDistributions(n)
// </vc-spec>
// <vc-code>
{
  ModThreeCases(n);
  DivModRelation(n, 3);
  MaxDistributionsDefinition(n);
  
  if n % 3 == 0 {
    result := 2 * (n / 3);
  } else {
    result := 2 * (n / 3) + 1;
  }
}
// </vc-code>

