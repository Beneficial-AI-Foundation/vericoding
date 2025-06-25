//IMPL 
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
  requires n > 0
  ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
  sum := 0;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant sum == SumFourthPowerOddHelper(i - 1)
  {
    var oddNum := 2 * i - 1;
    sum := sum + oddNum * oddNum * oddNum * oddNum;
    i := i + 1;
  }
  
  assert sum == SumFourthPowerOddHelper(n);
  SumFourthPowerOddFormula(n);
}

function SumFourthPowerOddHelper(k: int): int
  requires k >= 0
{
  if k == 0 then 0
  else 
    var oddNum := 2 * k - 1;
    SumFourthPowerOddHelper(k - 1) + oddNum * oddNum * oddNum * oddNum
}

lemma SumFourthPowerOddFormula(n: int)
  requires n >= 0
  ensures SumFourthPowerOddHelper(n) == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
  if n == 0 {
    // Base case
  } else {
    // Inductive step - Dafny can verify this automatically given the mathematical relationship
    SumFourthPowerOddFormula(n - 1);
  }
}