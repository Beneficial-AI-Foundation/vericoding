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
  if |numbers| == 0 {
    return 0;
  } else {
    var head := numbers[0];
    var tail := numbers[1..];
    var res_tail := prod_signs(tail);

    if head < 0 {
      // If head is negative, its sign flips the total product, but its abs value is added.
      // So, if res_tail was positive, the new product is negative. if res_tail negative, new product positive.
      // The sum_abs proof needs to be careful here too.
      // prod_signs(numbers) == -abs(head) * res_tail is not right, because res_tail already has the accumulated product of signs.
      // We need to multiply by head directly.
      return head * res_tail;
    } else {
      // If head is non-negative, its sign doesn't change the total product sign.
      return head * res_tail;
    }
  }
}
// </vc-code>

