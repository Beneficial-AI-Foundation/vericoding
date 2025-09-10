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
    // Work with numerators to avoid tricky division reasoning directly.
    assert 6 * TotalCubesForHeight(h + 1) == (h + 1) * (h + 2) * (h + 3);
    assert 6 * TotalCubesForHeight(h)     == h * (h + 1) * (h + 2);

    assert 6 * (TotalCubesForHeight(h + 1) - TotalCubesForHeight(h)) ==
           (h + 1) * (h + 2) * (h + 3) - h * (h + 1) * (h + 2);

    // Factor the difference.
    assert (h + 1) * (h + 2) * (h + 3) - h * (h + 1) * (h + 2) ==
           (h + 1) * (h + 2) * ((h + 3) - h);
    assert (h + 1) * (h + 2) * ((h + 3) - h) == (h + 1) * (h + 2) * 3;
    assert 6 * (TotalCubesForHeight(h + 1) - TotalCubesForHeight(h)) ==
           3 * (h + 1) * (h + 2);

    // Relate to CubesForLevel(h+1).
    assert 6 * CubesForLevel(h + 1) == 3 * (h + 1) * (h + 2);
    assert 6 * (TotalCubesForHeight(h + 1) - TotalCubesForHeight(h)) ==
           6 * CubesForLevel(h + 1);

    // Divide both sides by 6 (exact division) to conclude equality.
    assert (6 * (TotalCubesForHeight(h + 1) - TotalCubesForHeight(h))) / 6 ==
           (6 * CubesForLevel(h + 1)) / 6;
    assert (6 * (TotalCubesForHeight(h + 1) - TotalCubesForHeight(h))) / 6 ==
           TotalCubesForHeight(h + 1) - TotalCubesForHeight(h);
    assert (6 * CubesForLevel(h + 1)) / 6 == CubesForLevel(h + 1);

    assert TotalCubesForHeight(h + 1) - TotalCubesForHeight(h) == CubesForLevel(h + 1);

    // Prove CubesForLevel(h+1) >= 1 using h >= 1
    assert h + 1 >= 2;
    assert h + 2 >= 3;
    assert (h + 1) * (h + 2) >= 6;
    assert (h + 1) * (h + 2) / 2 >= 1;
    assert CubesForLevel(h + 1) >= 1;
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
    assert TotalCubesForHeight(h) > TotalCubesForHeight(oldh);
    // show the measure decreases
    Subtract_strict(n, TotalCubesForHeight(h), TotalCubesForHeight(oldh));
  }

  result := h;
}
// </vc-code>

