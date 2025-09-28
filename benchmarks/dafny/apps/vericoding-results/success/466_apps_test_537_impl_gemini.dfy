predicate ValidInput(n: int, k: int) {
    n >= 0 && k >= 0 && k + 1 > 0
}

predicate ValidOutput(result: seq<int>, n: int, k: int) {
    |result| == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

function OptimalDiplomas(n: int, k: int): int
    requires ValidInput(n, k)
{
    (n / 2) / (k + 1)
}

// <vc-helpers>
lemma LemmaDivMul(x: int, y: int)
    requires x >= 0 && y > 0
    ensures (x / y) * y <= x
{
    // This is a property of Euclidean division.
    // Given x = (x/y)*y + (x%y) and 0 <= x%y, it follows that (x/y)*y <= x.
    // Dafny's SMT solver can prove this lemma, which then helps in proving the main method's postconditions.
}

lemma LemmaHalfLe(x: int)
    requires x >= 0
    ensures x / 2 <= x
{
    // For x >= 0, we have x - x/2 >= 0.
    // Let d = x/2. x = 2*d + x%2.
    // x - d = d + x%2.
    // Since x >= 0, d = x/2 >= 0. And x%2 >= 0.
    // Therefore, d + x%2 >= 0, proving the lemma.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == OptimalDiplomas(n, k)
// </vc-spec>
// <vc-code>
{
  var a := (n / 2) / (k + 1);
  var b := a * k;
  var c := n - a - b;
  
  // Let's assert the properties to guide the verifier.
  var n_half := n / 2;
  var k_plus_1 := k + 1;
  
  // Prove result[0] + result[1] <= n / 2
  // This is a + b <= n_half, which is a * k_plus_1 <= n_half
  // Since a = n_half / k_plus_1, we need to show (n_half / k_plus_1) * k_plus_1 <= n_half
  // This is true by LemmaDivMul.
  LemmaDivMul(n_half, k_plus_1);
  assert a * k_plus_1 <= n_half;

  // Prove result[2] >= 0
  // This requires a + b <= n.
  // We know a + b <= n_half.
  // We need n_half <= n. This is true by LemmaHalfLe.
  LemmaHalfLe(n);
  assert n_half <= n;
  assert a + b <= n;

  result := [a, b, c];
}
// </vc-code>

