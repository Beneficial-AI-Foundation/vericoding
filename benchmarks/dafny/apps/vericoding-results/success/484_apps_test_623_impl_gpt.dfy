function CountValidMinutes(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 then 0
    else if a == 1 && b == 1 then 0
    else (if a > 1 || b > 1 then 1 else 0) + 
         CountValidMinutes(if a < b then a + 1 else a - 2, if a < b then b - 2 else b + 1)
}

// <vc-helpers>
lemma CountValidMinutes_nonneg(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures CountValidMinutes(a, b) >= 0
  decreases a + b
{
  if a <= 0 || b <= 0 {
    // CountValidMinutes(a,b) == 0
  } else if a == 1 && b == 1 {
    // CountValidMinutes(1,1) == 0
  } else {
    assert a > 0;
    assert b > 0;
    if a < b {
      assert a + 1 >= 0;
      assert a >= 1;
      assert b >= a + 1;
      assert a + 1 >= 2;
      assert b - 2 >= 0;
      CountValidMinutes_nonneg(a + 1, b - 2);
    } else {
      assert a >= 1 && b >= 1;
      if b >= 2 {
        assert a >= b;
        assert a >= 2;
      } else {
        assert b == 1;
        assert a != 1;
        assert a >= 1;
        assert a > 1;
        assert a >= 2;
      }
      assert a - 2 >= 0;
      assert b + 1 >= 0;
      CountValidMinutes_nonneg(a - 2, b + 1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int) returns (result: int)
    requires a1 >= 1 && a2 >= 1
    ensures result >= 0
    ensures result == CountValidMinutes(a1, a2)
    ensures (a1 == 1 && a2 == 1) ==> result == 0
// </vc-spec>
// <vc-code>
{
  CountValidMinutes_nonneg(a1, a2);
  result := CountValidMinutes(a1, a2);
  assert result >= 0;
  if a1 == 1 && a2 == 1 {
    assert result == 0;
  }
}
// </vc-code>

