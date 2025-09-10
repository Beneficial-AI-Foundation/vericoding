predicate ValidInput(n: int, k: int) {
    n >= 1 && k >= 2
}

function ImpossibilityCondition(n: int, k: int): bool
    requires ValidInput(n, k)
{
    2 * (n - 1) - k * (k - 1) > 0
}

predicate ValidSolution(n: int, k: int, result: int)
    requires ValidInput(n, k)
{
    if ImpossibilityCondition(n, k) then
        result == -1
    else
        result >= 0 && result <= k &&
        exists x: int :: 
            x >= 0 && 
            x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0 && 
            (x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0) &&
            result == k - x
}

// <vc-helpers>
lemma ValidSolutionImpossible(n: int, k: int, r: int)
    requires ValidInput(n, k)
    requires ImpossibilityCondition(n, k)
    requires r == -1
    ensures ValidSolution(n, k, r)
{
    reveal ImpossibilityCondition(n, k);
}

lemma ValidSolutionPossible(n: int, k: int, r: int)
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    requires r == k
    ensures ValidSolution(n, k, r)
{
    assert r >= 0;
    assert r <= k;

    reveal ImpossibilityCondition(n, k);
    var c := 2 * (n - 1) - k * (k - 1);
    assert !(c > 0);
    if c > 0 {
        assert false;
    } else {
        assert c <= 0;
    }
    assert 2 * (n - 1) - k * (k - 1) <= 0;

    assert exists x: int ::
        x >= 0 &&
        x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0 &&
        (x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0) &&
        r == k - x
    by {
        var x := 0;
        assert x >= 0;
        assert x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0;
        assert r == k - x;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= -1
    ensures (result == -1) <==> ImpossibilityCondition(n, k)
    ensures ValidSolution(n, k, result)
// </vc-spec>
// <vc-code>
{
  if ImpossibilityCondition(n, k) {
    result := -1;
    ValidSolutionImpossible(n, k, result);
  } else {
    result := k;
    ValidSolutionPossible(n, k, result);
  }
}
// </vc-code>

