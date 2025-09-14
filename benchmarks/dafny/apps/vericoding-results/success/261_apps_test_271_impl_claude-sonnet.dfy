predicate ValidResult(n: int, result: int)
  requires n >= 0
{
  var quotient := n / 10;
  var remainder := n % 10;
  result % 10 == 0 && 
  result >= 0 &&
  (remainder < 5 ==> result == quotient * 10) &&
  (remainder > 5 ==> result == (quotient + 1) * 10) &&
  (remainder == 5 ==> (quotient % 2 == 0 ==> result == quotient * 10) && 
                      (quotient % 2 == 1 ==> result == (quotient + 1) * 10))
}

// <vc-helpers>
lemma DivisionProperties(n: int)
  requires n >= 0
  ensures n == (n / 10) * 10 + (n % 10)
  ensures 0 <= n % 10 <= 9
{
}

lemma ValidResultHelper(n: int, quotient: int, remainder: int, result: int)
  requires n >= 0
  requires quotient == n / 10
  requires remainder == n % 10
  requires result % 10 == 0
  requires result >= 0
  requires (remainder < 5 ==> result == quotient * 10)
  requires (remainder > 5 ==> result == (quotient + 1) * 10)
  requires (remainder == 5 ==> (quotient % 2 == 0 ==> result == quotient * 10) && 
                               (quotient % 2 == 1 ==> result == (quotient + 1) * 10))
  ensures ValidResult(n, result)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 0
  ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  var quotient := n / 10;
  var remainder := n % 10;
  
  if remainder < 5 {
    result := quotient * 10;
  } else if remainder > 5 {
    result := (quotient + 1) * 10;
  } else {
    // remainder == 5
    if quotient % 2 == 0 {
      result := quotient * 10;
    } else {
      result := (quotient + 1) * 10;
    }
  }
  
  DivisionProperties(n);
  ValidResultHelper(n, quotient, remainder, result);
}
// </vc-code>

