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
    return 1;
  } else {
    var head := numbers[0];
    var tail := numbers[1..];
    var res_tail := prod_signs(tail);
    if head == 0 {
      return 0;
    } else {
      var num_negatives_tail := count_negatives(tail);
      var num_negatives_total := count_negatives(numbers);
      
      // Case 1: The head is positive
      if head > 0 {
        // If the product of the tail is positive, the overall product is positive.
        // If the product of the tail is negative, the overall product is negative.
        // The parity of negative numbers remains the same.
        assert (num_negatives_tail % 2 == 1 && res_tail <= 0) || (num_negatives_tail % 2 == 0 && res_tail >= 0);
        assert num_negatives_total == num_negatives_tail;
        return head * res_tail;
      } 
      // Case 2: The head is negative
      else { // head < 0
        // If the product of the tail is positive, the overall product is negative.
        // If the product of the tail is negative, the overall product is positive.
        // The parity of negative numbers flips.
        assert (num_negatives_tail % 2 == 1 && res_tail <= 0) || (num_negatives_tail % 2 == 0 && res_tail >= 0);
        assert num_negatives_total == num_negatives_tail + 1;
        return head * res_tail;
      }
    }
  }
}
// </vc-code>

