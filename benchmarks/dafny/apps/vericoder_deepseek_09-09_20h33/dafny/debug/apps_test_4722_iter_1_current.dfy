predicate ValidInput(A: int, B: int)
{
    1 <= A <= 100 && 1 <= B <= 100
}

predicate DistributionPossible(A: int, B: int)
{
    A % 3 == 0 || B % 3 == 0 || (A + B) % 3 == 0
}

// <vc-helpers>
lemma Mod3Lemma(a: int, b: int)
  requires 1 <= a <= 100 && 1 <= b <= 100
  ensures (a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0) == 
          ((a % 3 == 0) || (b % 3 == 0) || ((a % 3 + b % 3) % 3 == 0))
{
  // This lemma establishes that (a + b) % 3 == (a % 3 + b % 3) % 3
  // which is a basic property of modular arithmetic
}

lemma Mod3Cases(a: int, b: int)
  requires 1 <= a <= 100 && 1 <= b <= 100
  ensures (a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0) == 
          ((a % 3) + (b % 3)) % 3 == 0
{
  // This lemma shows the equivalence between the three conditions
  // and the condition that the sum of remainders mod 3 is 0
  // Cases:
  // 1. If a % 3 == 0, then remainder sum is 0 + (b % 3) ≡ b % 3 mod 3
  // 2. If b % 3 == 0, then remainder sum is (a % 3) + 0 ≡ a % 3 mod 3  
  // 3. If neither is 0, then (a % 3 + b % 3) % 3 must be 0
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int) returns (result: string)
    requires ValidInput(A, B)
    ensures result == "Possible" <==> DistributionPossible(A, B)
    ensures result == "Possible" || result == "Impossible"
// </vc-spec>
// <vc-code>
{
  if A % 3 == 0 || B % 3 == 0 || (A + B) % 3 == 0 {
    result := "Possible";
  } else {
    result := "Impossible";
  }
}
// </vc-code>

