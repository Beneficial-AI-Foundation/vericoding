predicate ValidInput(r: int, g: int, b: int) {
    r >= 0 && g >= 0 && b >= 0
}

function MaxTables(r: int, g: int, b: int): int
    requires ValidInput(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

function min(a: int, b: int): int {
    if a <= b then a else b
}

// <vc-helpers>
lemma MinLowerBound(a: int, b: int, lb: int)
  requires lb <= a && lb <= b
  ensures lb <= min(a, b)
{
  if a <= b {
    assert min(a, b) == a;
  } else {
    assert min(a, b) == b;
  }
}

lemma MaxTablesNonNeg(r: int, g: int, b: int)
  requires ValidInput(r, g, b)
  ensures MaxTables(r, g, b) >= 0
{
  assert (r + g + b) / 3 >= 0;
  assert r + g >= 0;
  assert r + b >= 0;
  assert g + b >= 0;

  MinLowerBound((r + g + b) / 3, r + g, 0);
  MinLowerBound(min((r + g + b) / 3, r + g), r + b, 0);
  MinLowerBound(min(min((r + g + b) / 3, r + g), r + b), g + b, 0);
}
// </vc-helpers>

// <vc-spec>
method solve(r: int, g: int, b: int) returns (result: int)
    requires ValidInput(r, g, b)
    ensures result == MaxTables(r, g, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := MaxTables(r, g, b);
  MaxTablesNonNeg(r, g, b);
}
// </vc-code>

