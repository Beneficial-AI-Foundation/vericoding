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
  ensures (if a <= b then (if a <= c then a else c) else (if b <= c then b else c)) == (if a <= (if b <= c then b else c) then a else (if b <= c then b else c))
{
}

lemma min_lemma_1(a: int, b: int, c: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures (if a <= b then (if a <= c then a else c) else (if b <= c then b else c)) <= a 
  && (if a <= b then (if a <= c then a else c) else (if b <= c then b else c)) <= b 
  && (if a <= b then (if a <= c then a else c) else (if b <= c then b else c)) <= c
{
}

lemma min_lemma_2(a: int, b: int)
  requires 0 <= a <= b || 0 <= b <= a
  ensures (if a <= b then a else b) >= 0
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
  ensures OptimalSum(k2, k3, k5, k6) == 256 * (if k2 <= k5 then (if k2 <= k6 then k2 else k6) else (if k5 <= k6 then k5 else k6)) + 32 * (if k3 <= (k2 - (if k2 <= k5 then (if k2 <= k6 then k2 else k6) else (if k5 <= k6 then k5 else k6))) then k3 else (k2 - (if k2 <= k5 then (if k2 <= k6 then k2 else k6) else (if k5 <= k6 then k5 else k6))))
{
}

function min(a: int, b: int): int
{
  if a <= b then a else b
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

