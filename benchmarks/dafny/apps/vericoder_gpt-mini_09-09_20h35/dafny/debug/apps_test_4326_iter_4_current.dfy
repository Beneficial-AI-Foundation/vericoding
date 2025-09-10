predicate ValidInput(n: int) {
    1 <= n <= 1000
}

function MaxGroupsWithAtLeastThree(n: int): int
    requires ValidInput(n)
{
    n / 3
}

predicate ValidSolution(n: int, result: int) 
    requires ValidInput(n)
{
    result == MaxGroupsWithAtLeastThree(n) &&
    result >= 0 &&
    result <= n
}

// <vc-helpers>
lemma MaxGroupsProperties(n: int)
  requires ValidInput(n)
  ensures ValidSolution(n, MaxGroupsWithAtLeastThree(n))
{
  // unfold definition
  assert MaxGroupsWithAtLeastThree(n) == n / 3;
  // n >= 1 implies n/3 >= 0
  assert 0 <= n / 3;
  // n/3 <= n for all integers n
  assert n / 3 <= n;
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  result := MaxGroupsWithAtLeastThree(n);
  return;
}
// </vc-code>

