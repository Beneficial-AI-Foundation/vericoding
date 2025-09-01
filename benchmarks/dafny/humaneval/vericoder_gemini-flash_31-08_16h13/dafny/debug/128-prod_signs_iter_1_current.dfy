function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
  ensures x >= 0 ==> abs(x) == x
  ensures x < 0 ==> abs(x) == -x
{
  if x >= 0 then x else -x
}
function sum_abs(s: seq<int>) : int
  ensures sum_abs(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_abs(s[1..])
}

// <vc-helpers>
function count_negatives(s: seq<int>): (count: nat)
  ensures count == |set i | 0 <= i < |s| && s[i] < 0|
{
  if |s| == 0 then 0
  else (if s[0] < 0 then 1 else 0) + count_negatives(s[1..])
}
// </vc-helpers>

// <vc-spec>
method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
// </vc-spec>
// <vc-code>
{
  var result := 0;
  var product_abs := 1;
  var negative_count := 0;

  if |numbers| == 0 {
    return 0;
  }

  // Calculate sum_abs(numbers) and count negatives
  // A loop invariant is tricky here becaues sum_abs uses recursion
  // The recursive definition makes the `sum_abs` contract difficult to work with
  // directly in a loop invariant. However, we can use the `forall` quantifier
  // to express properties of the elements and combine them.
  // We can calculate sum_abs(numbers) and negative_count iteratively
  // and prove that product_abs eventually holds sum_abs based on the definition of prod_signs
  // We can use a recursive function in helpers to prove count_negatives correct
  // However, for brevity, we can compute them directly below in the loop.

  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant product_abs == sum_abs(numbers[0..i])
    invariant negative_count == count_negatives(numbers[0..i])
    decreases |numbers| - i
  {
    product_abs := product_abs + abs(numbers[i]);
    if numbers[i] < 0 {
      negative_count := negative_count + 1;
    }
    i := i + 1;
  }

  // After the loop, product_abs == sum_abs(numbers), and negative_count == |set i | 0 <= i < |numbers| && numbers[i] < 0|
  // so we can now determine the sign.
  if negative_count % 2 == 1 {
    result := -product_abs;
  } else {
    result := product_abs;
  }

  return result;
}
// </vc-code>

