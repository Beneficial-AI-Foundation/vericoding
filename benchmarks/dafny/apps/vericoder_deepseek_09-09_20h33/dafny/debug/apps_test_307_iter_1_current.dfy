predicate ValidInput(k2: int, k3: int, k5: int, k6: int)
{
    k2 >= 0 && k3 >= 0 && k5 >= 0 && k6 >= 0 &&
    k2 <= 5000000 && k3 <= 5000000 && k5 <= 5000000 && k6 <= 5000000
}

function OptimalSum(k2: int, k3: int, k5: int, k6: int): int
    requires ValidInput(k2, k3, k5, k6)
{
    var count256 := min(min(k2, k5), k6);
    var remaining_k2 := k2 - count256;
    var count32 := min(k3, remaining_k2);
    256 * count256 + 32 * count32
}

// <vc-helpers>
lemma min_lemma_0(a: int, b: int, c: int)
  ensures min(min(a, b), c) == min(a, min(b, c))
{
}

lemma min_lemma_1(a: int, b: int, c: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures min(min(a, b), c) <= a && min(min(a, b), c) <= b && min(min(a, b), c) <= c
{
}

lemma min_lemma_2(a: int, b: int)
  requires 0 <= a <= b || 0 <= b <= a
  ensures min(a, b) >= 0
{
}

lemma subtraction_lemma(a: int, b: int)
  requires a >= b >= 0
  ensures a - b >= 0
{
}

lemma non_negative_product(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a * b >= 0
{
}

lemma addition_lemma(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a + b >= 0
{
}

lemma optimal_sum_properties(k2: int, k3: int, k5: int, k6: int)
  requires ValidInput(k2, k3, k5, k6)
  ensures OptimalSum(k2, k3, k5, k6) == 256 * min(min(k2, k5), k6) + 32 * min(k3, k2 - min(min(k2, k5), k6))
{
}
// </vc-helpers>

// <vc-spec>
method solve(k2: int, k3: int, k5: int, k6: int) returns (result: int)
    requires ValidInput(k2, k3, k5, k6)
    ensures result >= 0
    ensures result == OptimalSum(k2, k3, k5, k6)
// </vc-spec>
// <vc-code>
{
  var count256 := min(min(k2, k5), k6);
  var remaining_k2 := k2 - count256;
  var count32 := min(k3, remaining_k2);
  result := 256 * count256 + 32 * count32;
}
// </vc-code>

