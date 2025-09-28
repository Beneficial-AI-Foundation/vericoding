// <vc-preamble>
function sumOfDigits(n: int): int
  requires n >= 0
  ensures n > 0 ==> sumOfDigits(n) > 0
  ensures n == 0 ==> sumOfDigits(n) == 0
{
  if n == 0 then 0
  else (n % 10) + sumOfDigits(n / 10)
}

predicate ValidInput(N: int)
{
  N >= 1
}

predicate IsDivisibleByDigitSum(N: int)
  requires N >= 1
{
  N % sumOfDigits(N) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
  requires ValidInput(N)
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> IsDivisibleByDigitSum(N)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation error by adding curly braces to the if statement */
  if IsDivisibleByDigitSum(N) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>
