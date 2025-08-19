//IMPL
//Problem 01
method sumOdds(n: nat) returns (sum: nat)
  requires n > 0
  ensures sum == n * n
{
  sum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum == i * i
  {
    sum := sum + (2 * i + 1);
    i := i + 1;
  }
}