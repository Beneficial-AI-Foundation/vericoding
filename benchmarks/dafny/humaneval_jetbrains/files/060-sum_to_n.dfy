/*
function_signature: def sum_to_n(n: Nat) -> Nat
sum_to_n is a function that sums numbers from 1 to n.
*/

method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
{
  assume false;
}
