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

lemma Lemma_MinProperties2(x: int, y: int, z: int)
  ensures (if y <= z then y else z) == (if z <= y then z else y)
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
  
  if r == 0 {
    assert ((n + m - 1) / m) == k;
  } else {
    assert ((n + m - 1) / m) == k + 1;
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
  
  if all_single <= all_multi && all_single <= mixed {
    result := all_single;
  } else if all_multi <= mixed {
    result := all_multi;
  } else {
    result := mixed;
  }
}
// </vc-code>

