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
  var product_abs_so_far := 0; // Renamed to accurately reflect accumulation
  var negative_count := 0;

  if |numbers| == 0 {
    return 0;
  }

  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant product_abs_so_far == sum_abs(numbers[0..i])
    invariant negative_count == count_negatives(numbers[0..i])
    decreases |numbers| - i
  {
    product_abs_so_far := product_abs_so_far + abs(numbers[i]);
    if numbers[i] < 0 {
      negative_count := negative_count + 1;
    }
    i := i + 1;
  }

  // After the loop, product_abs_so_far == sum_abs(numbers), and negative_count == |set i | 0 <= i < |numbers| && numbers[i] < 0|
  // so we can now determine the sign.
  if negative_count % 2 == 1 {
    result := -product_abs_so_far;
  } else {
    result := product_abs_so_far;
  }

  return result;
}
// </vc-code>

