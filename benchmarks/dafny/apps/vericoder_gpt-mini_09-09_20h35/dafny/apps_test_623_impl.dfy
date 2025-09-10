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
    // CountValidMinutes returns 0 here
  } else if a == 1 && b == 1 {
    // CountValidMinutes returns 0 here
  } else {
    // Now a > 0 and b > 0, and not (a == 1 && b == 1)
    if a < b {
      // prove b >= 2
      assert a > 0;
      if b == 1 {
        // from b == 1 and a < b we get a < 1, hence a <= 0, contradicting a > 0
        assert a < 1;
        assert a <= 0;
        assert false;
      }
      assert b >= 2;
      assert b - 2 >= 0;
      CountValidMinutes_nonneg(a + 1, b - 2);
    } else {
      // a >= b and a > 0
      assert a > 0;
      if a == 1 {
        // then b <= a == 1, so b == 1, contradicting the (a == 1 && b == 1) case
        assert b <= 1;
        assert b == 1;
        assert false;
      }
      assert a >= 2;
      assert a - 2 >= 0;
      CountValidMinutes_nonneg(a - 2, b + 1);
    }
    // the added 0 or 1 ensures the whole sum is still >= 0 given the recursive call is >= 0
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
}
// </vc-code>

