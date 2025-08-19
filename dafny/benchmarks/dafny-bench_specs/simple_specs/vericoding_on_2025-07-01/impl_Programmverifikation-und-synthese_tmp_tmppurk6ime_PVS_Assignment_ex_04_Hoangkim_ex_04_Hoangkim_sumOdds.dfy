//IMPL
//Problem 01
method sumOdds(n: nat) returns (sum: nat)
  requires n > 0
  ensures sum == n * n
{
  sum := 0;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant sum == (i - 1) * (i - 1)
  {
    sum := sum + (2 * i - 1);
    i := i + 1;
  }
}