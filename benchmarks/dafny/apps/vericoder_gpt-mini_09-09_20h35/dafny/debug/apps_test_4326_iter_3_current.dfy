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
  assert MaxGroupsWithAtLeastThree(n) == n / 3;
  assert 0 <= n / 3;
  assert n / 3 <= n;
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  return MaxGroupsWithAtLeastThree(n);
}
// </vc-code>

