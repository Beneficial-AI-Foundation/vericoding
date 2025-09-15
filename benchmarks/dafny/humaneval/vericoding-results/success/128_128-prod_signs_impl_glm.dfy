// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): changed count_negatives to use set expression */
function count_negatives(nums: seq<int>): int
{
  |set i | 0 <= i < |nums| && nums[i] < 0|
}
function sign_from_count(count: int): int
  requires count >= 0
  ensures abs(sign_from_count(count)) == 1
  ensures count % 2 == 1 ==> sign_from_count(count) == -1
  ensures count % 2 == 0 ==> sign_from_count(count) == 1
{
  if count % 2 == 0 then 1 else -1
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
  /* code modified by LLM (iteration 3): updated helpers to fix postcondition proofs */
  var negative_count := count_negatives(numbers);
  var abs_sum := sum_abs(numbers);
  var sign := sign_from_count(negative_count);
  s := sign * abs_sum;
}
// </vc-code>
