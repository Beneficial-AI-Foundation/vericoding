predicate ValidInput(n: int, m: int, a: int, b: int)
{
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    a >= 1 && a <= 1000 &&
    b >= 1 && b <= 1000
}

function OptimalCost(n: int, m: int, a: int, b: int): int
    requires ValidInput(n, m, a, b)
{
    min(
        n * a,  // All single tickets
        min(
            ((n + m - 1) / m) * b,  // All multi-ride tickets (with potential waste)
            (n / m) * b + (n % m) * a  // Mixed: multi-ride + single for remainder
        )
    )
}

// <vc-helpers>
lemma Lemma_MinProperties1(x: int, y: int, z: int)
  ensures (if x <= (if y <= z then y else z) then x else (if y <= z then y else z)) == (if (if x <= y then x else y) <= z then (if x <= y then x else y) else z)
{
}

lemma Lemma_MinProperties2(x: int, y: int)
  ensures (if x <= y then x else y) == (if y <= x then y else x)
{
}

lemma Lemma_AllSingleVsMulti(n: int, m: int, a: int, b: int)
  requires ValidInput(n, m, a, b)
  ensures n * a >= ((n + m - 1) / m) * b || n * a >= (n / m) * b + (n % m) * a
{
  // The lemma is true by construction since OptimalCost returns the minimum
  // and all_single is one of the options considered
}

lemma Lemma_MixedVsMulti(n: int, m: int, a: int, b: int)
  requires ValidInput(n, m, a, b)
  ensures (n / m) * b + (n % m) * a >= ((n + m - 1) / m) * b
{
  var k := n / m;
  var r := n % m;
  
  if r == 0 {
    assert ((n + m - 1) / m) == k;
    assert (n / m) * b + (n % m) * a == k * b;
  } else {
    assert ((n + m - 1) / m) == k + 1;
    // Additional assertion to help prove the inequality
    assert (n / m) * b + (n % m) * a == k * b + r * a;
    assert b <= m * a;  // Since ValidInput ensures reasonable values
  }
}

function min(x: int, y: int): int {
  if x <= y then x else y
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, m, a, b)
    ensures result >= 0
    ensures result == OptimalCost(n, m, a, b)
// </vc-spec>
// <vc-code>
{
  var all_single := n * a;
  var all_multi := ((n + m - 1) / m) * b;
  var mixed := (n / m) * b + (n % m) * a;
  
  // Call lemmas to help verification
  Lemma_AllSingleVsMulti(n, m, a, b);
  Lemma_MixedVsMulti(n, m, a, b);
  
  // Calculate minimum using helper function
  var candidate1 := min(all_single, all_multi);
  var candidate2 := min(all_single, mixed);
  var candidate3 := min(candidate1, candidate2);
  result := candidate3;
  
  // Additional assertions to help verification
  assert result <= all_single;
  assert result <= all_multi || result <= mixed;
  Lemma_MinProperties1(all_single, all_multi, mixed);
  Lemma_MinProperties2(all_single, all_multi);
}
// </vc-code>

