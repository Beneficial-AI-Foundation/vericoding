function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification

// <vc-helpers>
lemma StairsLemma(n: nat)
  ensures Stairs(n) >= 1
{
  if n <= 1 {
  } else {
    StairsLemma(n-1);
  }
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
  } else {
    var a: nat;
    var b: nat;
    a := ClimbStairs(n - 2);
    b := ClimbStairs(n - 1);
    r := a + b;
  }
}
// </vc-code>

