function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification

// <vc-helpers>
lemma StairsNonNegative(n: nat)
  ensures Stairs(n) >= 1
{
  if n <= 1 {
    assert Stairs(n) == 1;
  } else {
    calc {
      Stairs(n);
      == Stairs(n - 2) + Stairs(n - 1);
      >= { StairsNonNegative(n - 2); StairsNonNegative(n - 1); }
         1 + 1;
      == 2;
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method ClimbStairsImpl(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{
  if n <= 1 {
    r := 1;
  } else {
    var a := ClimbStairsImpl(n - 2);
    var b := ClimbStairsImpl(n - 1);
    r := a + b;
  }
}
// </vc-code>
