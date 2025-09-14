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
lemma TgeH(h: int)
  requires h >= 1
  ensures TotalCubesForHeight(h) >= h
{
  assert h >= 1;
  assert h + 1 >= 2;
  assert h + 2 >= 3;

  assert 0 <= h;
  assert 0 <= h + 1;
  assert 0 <= h + 2;

  var s1 := h * (h + 1);
  assert s1 >= h * 2; // using (h+1) >= 2 and h >= 0

  var s := s1 * (h + 2);
  assert s >= (h * 2) * 3; // using (h+2) >= 3 and s1 >= h*2 >= 0

  assert (h * 2) * 3 == h * 6;
  assert s >= 6 * h;

  assert TotalCubesForHeight(h) == s / 6;
  assert 6 > 0;
  assert s / 6 >= (6 * h) / 6;
  assert (6 * h) / 6 == h;
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
  while TotalCubesForHeight(h + 1) <= n
    invariant h >= 1
    invariant TotalCubesForHeight(h) <= n
    invariant h <= n
    decreases n - h
  {
    h := h + 1;
    TgeH(h);
    assert TotalCubesForHeight(h) <= n;
    assert h <= n;
  }
  result := h;
}
// </vc-code>

