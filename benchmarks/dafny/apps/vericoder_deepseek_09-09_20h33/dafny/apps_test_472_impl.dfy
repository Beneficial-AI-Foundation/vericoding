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
    var sum := (x % 10) + digitSum(x / 10);
    if x >= 10 {
      assert x % 10 <= 9;
      assert 9 + (x / 10) <= x;
    } else {
      assert x < 10;
      assert x % 10 == x;
    }
  }
}

lemma digitSumPositiveForXGe10(x: int)
  requires x >= 10
  ensures digitSum(x) > 0
  decreases x
{
  digitSumNonNegative(x / 10);
}

predicate ValidSolution(x: int, n: int) 
{
  x > 0 && x * x + digitSum(x) * x == n
}

lemma quadraticGrowth(x: int, n: int)
  requires x >= 1
  requires n >= 1
  ensures x * x + digitSum(x) * x >= x * x
  decreases x
{
  digitSumNonNegative(x);
}

lemma monotonicGrowth(x: int)
  requires x >= 1
  ensures x * x + digitSum(x) * x <= (x+1) * (x+1) + digitSum(x+1) * (x+1)
{
  digitSumNonNegative(x);
  digitSumNonNegative(x+1);
  
  var left := x * x + digitSum(x) * x;
  var right := (x+1) * (x+1) + digitSum(x+1) * (x+1);
  
  assert (x+1)*(x+1) > x*x;
  assert digitSum(x+1) >= 0;
  
  digitSumUpperBound(x);
  assert digitSum(x) <= x;
  
  if x >= 2 {
    assert x*x + x*x <= x*x + x*x;
    calc {
      (x+1)*(x+1);
      ==
      x*x + 2*x + 1;
      > 
      x*x + x*x;
      >=
      x*x + digitSum(x)*x;
    }
  }
  
  if x == 1 {
    assert left == 1*1 + digitSum(1)*1;
    assert digitSum(1) == 1;
    assert left == 2;
    assert right == 4 + digitSum(2)*2;
    assert digitSum(2) == 2;
    assert right == 8;
  }
}

lemma growthLemma(y: int, y_max: int, n: int)
  requires y >= y_max
  requires y_max >= 1
  requires y_max * y_max > n
  ensures y * y + digitSum(y) * y > n
{
  digitSumNonNegative(y);
  assert y * y >= y_max * y_max;
  assert y * y > n;
  assert y * y + digitSum(y) * y >= y * y;
}

lemma squareGrowth(x: int, n: int)
  requires x >= 1
  requires x * x > n
  ensures x * x + digitSum(x) * x > n
{
  digitSumNonNegative(x);
  assert x * x + digitSum(x) * x >= x * x;
}
// </vc-helpers>
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
  var f := 0;
  
  while x * x <= n
    invariant 1 <= x
    invariant result == -1
    invariant forall y :: 1 <= y < x ==> y * y + digitSum(y) * y != n
    decreases n - x
  {
    f := x * x + digitSum(x) * x;
    
    if f == n {
      result := x;
      return;
    } 
    
    if f > n {
      break;
    }
    
    x := x + 1;
  }
  
  // Check if we found the solution in the loop
  if result != -1 {
    return;
  }
  
  // Prove no solution exists for larger values
  ghost var y_max := x;
  
  // Use squareGrowth instead of growthLemma for the general case
  ghost var z_max := if x * x > n then x else x + 1;
  squareGrowth(z_max, n);
  
  ghost var y := z_max;
  while y >= z_max
    invariant y >= z_max
    invariant forall z :: z >= y ==> z * z + digitSum(z) * z > n
    decreases 0
  {
    squareGrowth(y, n);
    y := y + 1;
  }
}
// </vc-code>

