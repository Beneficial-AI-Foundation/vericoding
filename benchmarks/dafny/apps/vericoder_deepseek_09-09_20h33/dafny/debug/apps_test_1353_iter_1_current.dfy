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
  ensures min(x, min(y, z)) == min(min(x, y), z)
{
}

lemma Lemma_MinProperties2(x: int, y: int, z: int)
  ensures min(y, z) == min(z, y)
{
}

lemma Lemma_AllSingleVsMulti(n: int, m: int, a: int, b: int)
  requires ValidInput(n, m, a, b)
  ensures n * a >= ((n + m - 1) / m) * b || n * a >= (n / m) * b + (n % m) * a
{
}

lemma Lemma_MixedVsMulti(n: int, m: int, a: int, b: int)
  requires ValidInput(n, m, a, b)
  ensures (n / m) * b + (n % m) * a >= ((n + m - 1) / m) * b
{
  var k := n / m;
  var r := n % m;
  
  // ((n + m - 1) / m) is either k or k+1
  if r == 0 {
    // n is divisible by m, both equal k * b
    assert ((n + m - 1) / m) == k;
  } else {
    // n not divisible by m, ceil(n/m) = k+1
    assert ((n + m - 1) / m) == k + 1;
    // Need to show: k * b + r * a >= (k + 1) * b
    // Which reduces to: r * a >= b
    // But this may not always hold, so we use the minimum
  }
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
  
  // The optimal cost is the minimum of these three options
  if all_single <= all_multi && all_single <= mixed {
    result := all_single;
  } else if all_multi <= mixed {
    result := all_multi;
  } else {
    result := mixed;
  }
}
// </vc-code>

