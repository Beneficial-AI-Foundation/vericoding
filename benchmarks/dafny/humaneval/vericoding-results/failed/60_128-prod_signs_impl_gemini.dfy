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
/* helper modified by LLM (iteration 5): [moved ensures from lemma to function and removed lemma] */
function CountNegatives(s: seq<int>): nat
  ensures CountNegatives(s) == |set i | 0 <= i < |s| && s[i] < 0|
{
  if |s| == 0 then 0
  else (if s[0] < 0 then 1 else 0) + CountNegatives(s[1..])
}
// </vc-helpers>

// <vc-spec>
method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [removed redundant lemma call] */
{
  var neg_count := CountNegatives(numbers);
  var total_sum := sum_abs(numbers);

  if neg_count % 2 == 0 {
    s := total_sum;
  } else {
    s := -total_sum;
  }
}
// </vc-code>
