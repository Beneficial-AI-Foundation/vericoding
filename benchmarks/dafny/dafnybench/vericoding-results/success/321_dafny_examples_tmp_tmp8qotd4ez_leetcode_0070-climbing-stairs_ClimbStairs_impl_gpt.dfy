function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification

// <vc-helpers>
lemma StepLemma(i: nat)
  requires i >= 2
  ensures Stairs(i) == Stairs(i - 2) + Stairs(i - 1)
{
  assert i > 1;
  assert Stairs(i) == Stairs(i - 2) + Stairs(i - 1);
}
// </vc-helpers>

// <vc-spec>
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    r := 1;
    assert r == Stairs(n);
  } else {
    var i: nat := 2;
    var a: nat := 1; // Stairs(0)
    var b: nat := 1; // Stairs(1)
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == Stairs(i - 2)
      invariant b == Stairs(i - 1)
      decreases n - i + 1
    {
      StepLemma(i);
      var c: nat := a + b;
      a := b;
      b := c;
      i := i + 1;
    }
    r := b;
    assert r == Stairs(n);
  }
}
// </vc-code>

