predicate ValidInput(n: int) {
    n >= 1
}

function CubesForLevel(level: int): int
    requires level >= 1
{
    level * (level + 1) / 2
}

function TotalCubesForHeight(h: int): int
    requires h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

predicate ValidPyramidHeight(n: int, h: int) {
    ValidInput(n) && h >= 1 && 
    TotalCubesForHeight(h) <= n &&
    TotalCubesForHeight(h + 1) > n
}

// <vc-helpers>
lemma Total_increase(h: int)
    requires h >= 1
    ensures TotalCubesForHeight(h + 1) - TotalCubesForHeight(h) == CubesForLevel(h + 1)
    ensures CubesForLevel(h + 1) >= 1
{
    // Work with a common numerator to help the prover with the algebraic simplification
    assert TotalCubesForHeight(h + 1) - TotalCubesForHeight(h)
        == ((h + 1) * (h + 2) * (h + 3) - h * (h + 1) * (h + 2)) / 6;
    // The numerator simplifies to 3 * (h+1) * (h+2)
    assert ((h + 1) * (h + 2) * (h + 3) - h * (h + 1) * (h + 2)) / 6
        == (3 * (h + 1) * (h + 2)) / 6;
    assert (3 * (h + 1) * (h + 2)) / 6 == (h + 1) * (h + 2) / 2;
    assert (h + 1) * (h + 2) / 2 == CubesForLevel(h + 1);
    assert CubesForLevel(h + 1) >= 1;
}

lemma Total_monotone(h: int)
    requires h >= 1
    ensures TotalCubesForHeight(h + 1) > TotalCubesForHeight(h)
{
    Total_increase(h);
    assert TotalCubesForHeight(h + 1) - TotalCubesForHeight(h) == CubesForLevel(h + 1);
    assert CubesForLevel(h + 1) >= 1;
    assert TotalCubesForHeight(h + 1) - TotalCubesForHeight(h) > 0;
}

lemma Subtract_strict(n: int, A: int, B: int)
    requires A > B
    ensures n - A < n - B
{
    assert (n - A) - (n - B) == B - A;
    assert B - A < 0;
    assert (n - A) - (n - B) < 0;
    assert n - A < n - B;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures ValidPyramidHeight(n, result)
// </vc-spec>
// <vc-code>
{
  var h := 1;
  // initial invariant: TotalCubesForHeight(1) == 1 and n >= 1
  assert TotalCubesForHeight(h) == 1;
  assert TotalCubesForHeight(h) <= n;

  while TotalCubesForHeight(h + 1) <= n
    invariant h >= 1
    invariant TotalCubesForHeight(h) <= n
    decreases n - TotalCubesForHeight(h)
  {
    var oldh := h;
    assert oldh >= 1;
    h := h + 1;
    Total_monotone(oldh);
    // show the measure decreases
    Subtract_strict(n, TotalCubesForHeight(h), TotalCubesForHeight(oldh));
  }

  result := h;
}
// </vc-code>

