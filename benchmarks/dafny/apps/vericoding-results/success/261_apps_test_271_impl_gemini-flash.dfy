// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function ComputeResult(n: int): int
  requires n >= 0
{
  var quotient := n / 10;
  var remainder := n % 10;
  if remainder < 5 then
    quotient * 10
  else if remainder > 5 then
    (quotient + 1) * 10
  else
    if quotient % 2 == 0 then
      quotient * 10
    else
      (quotient + 1) * 10
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 0
  ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  result := ComputeResult(n);
}
// </vc-code>
