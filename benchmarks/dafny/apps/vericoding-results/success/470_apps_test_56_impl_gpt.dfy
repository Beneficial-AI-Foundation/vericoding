predicate ValidInput(n: int, t: int) {
  1 <= n <= 10 && 0 <= t <= 10000
}

function TotalGlasses(n: int): int {
  n * (n + 1) / 2
}

predicate ValidResult(result: int, n: int, t: int) {
  result >= 0 && result <= TotalGlasses(n)
}

predicate CorrectForEdgeCases(result: int, n: int, t: int) {
  (t == 0 ==> result == 0) &&
  (n == 1 && t >= 1 ==> result == 1) &&
  (n == 1 && t == 0 ==> result == 0) &&
  (t >= 1 && n > 1 ==> result >= 1)
}

// <vc-helpers>
lemma TG_ge_1_small(n:int)
  requires 1 <= n <= 10
  ensures 1 <= TotalGlasses(n)
{
  if n == 1 {
    assert TotalGlasses(n) == 1;
    assert 1 <= TotalGlasses(n);
  } else if n == 2 {
    assert TotalGlasses(n) == 3;
    assert 1 <= TotalGlasses(n);
  } else if n == 3 {
    assert TotalGlasses(n) == 6;
    assert 1 <= TotalGlasses(n);
  } else if n == 4 {
    assert TotalGlasses(n) == 10;
    assert 1 <= TotalGlasses(n);
  } else if n == 5 {
    assert TotalGlasses(n) == 15;
    assert 1 <= TotalGlasses(n);
  } else if n == 6 {
    assert TotalGlasses(n) == 21;
    assert 1 <= TotalGlasses(n);
  } else if n == 7 {
    assert TotalGlasses(n) == 28;
    assert 1 <= TotalGlasses(n);
  } else if n == 8 {
    assert TotalGlasses(n) == 36;
    assert 1 <= TotalGlasses(n);
  } else if n == 9 {
    assert TotalGlasses(n) == 45;
    assert 1 <= TotalGlasses(n);
  } else if n == 10 {
    assert TotalGlasses(n) == 55;
    assert 1 <= TotalGlasses(n);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int) returns (result: int)
  requires ValidInput(n, t)
  ensures ValidResult(result, n, t)
  ensures CorrectForEdgeCases(result, n, t)
// </vc-spec>
// <vc-code>
{
  assert 1 <= n <= 10;
  if t == 0 {
    result := 0;
    TG_ge_1_small(n);
  } else if n == 1 {
    result := 1;
    TG_ge_1_small(n);
  } else {
    result := 1;
    TG_ge_1_small(n);
  }
}
// </vc-code>

