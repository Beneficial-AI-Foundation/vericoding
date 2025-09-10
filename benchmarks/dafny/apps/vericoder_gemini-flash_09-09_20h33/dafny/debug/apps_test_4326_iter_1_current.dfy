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
function MaxGroupsWithAtLeastThree(n: int): int
    requires 1 <= n <= 1000
{
    n / 3
}

predicate ValidSolution(n: int, result: int)
    requires 1 <= n <= 1000
{
    result == MaxGroupsWithAtLeastThree(n) &&
    result >= 0 &&
    result <= n
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var result := n / 3;
  return result;
}
// </vc-code>

