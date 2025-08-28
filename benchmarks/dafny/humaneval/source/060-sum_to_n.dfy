method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
{
  // impl-start
  r := n * (n + 1) / 2;
  // impl-end
}
