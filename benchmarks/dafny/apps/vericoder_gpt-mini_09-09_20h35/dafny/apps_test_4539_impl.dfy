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

// <vc-helpers>
// No helper functions required for this verification.
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
  requires ValidInput(N)
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> IsDivisibleByDigitSum(N)
// </vc-spec>
// <vc-code>
{
  var s := sumOfDigits(N);
  if N % s == 0 {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

