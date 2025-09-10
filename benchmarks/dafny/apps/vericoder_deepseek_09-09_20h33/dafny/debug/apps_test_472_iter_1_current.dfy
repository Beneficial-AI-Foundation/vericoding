function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

// <vc-helpers>
lemma digitSumNonNegative(x: int)
  requires x >= 0
  ensures digitSum(x) >= 0
  decreases x
{
  if x > 0 {
    digitSumNonNegative(x / 10);
  }
}

lemma digitSumUpperBound(x: int)
  requires x >= 0
  ensures digitSum(x) <= x
  decreases x
{
  if x > 0 {
    digitSumUpperBound(x / 10);
    assert digitSum(x) == (x % 10) + digitSum(x / 10);
    assert digitSum(x / 10) <= x / 10;
    assert (x % 10) <= 9;
    assert (x % 10) + digitSum(x / 10) <= 9 + (x / 10);
    assert 9 + (x / 10) <= x;
  }
}

predicate ValidSolution(x: int, n: int) 
{
  x > 0 && x * x + digitSum(x) * x == n
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures n == 1 ==> result == -1
  ensures n > 1 && result > 0 ==> result * result + digitSum(result) * result == n
  ensures n > 1 && result > 0 ==> forall y :: y > 0 && y < result ==> y * y + digitSum(y) * y != n
  ensures n > 1 && result == -1 ==> forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  ensures result == -1 || result > 0
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := -1;
    return;
  }
  
  var x := 1;
  result := -1;
  
  while x * x <= n
    invariant 1 <= x <= n + 1
    invariant x > 1 ==> forall y :: 1 <= y < x ==> y * y + digitSum(y) * y != n
    invariant result == -1 || result > 0
    decreases n - x
  {
    var f := x * x + digitSum(x) * x;
    
    if f == n {
      result := x;
      return;
    } 
    
    if f > n {
      break;
    }
    
    x := x + 1;
  }
  
  if result == -1 {
    // Verify the universal quantifier for the case when no solution exists
    var temp := 1;
    ghost var all_fail := true;
    while temp * temp <= n
      invariant 1 <= temp <= n + 1
      invariant forall y :: 1 <= y < temp ==> y * y + digitSum(y) * y != n
      invariant all_fail
      decreases n - temp
    {
      if temp * temp + digitSum(temp) * temp == n {
        all_fail := false;
        result := temp;
        return;
      }
      
      if temp * temp + digitSum(temp) * temp > n {
        break;
      }
      
      temp := temp + 1;
    }
  }
}
// </vc-code>

