// <vc-preamble>
function digitToChar(digit: int): char
  requires 0 <= digit <= 9
{
  (('0' as int) + digit) as char
}

function intToStringHelper(n: int): string
  requires n > 0
  decreases n
{
  if n < 10 then [digitToChar(n)]
  else intToStringHelper(n / 10) + [digitToChar(n % 10)]
}

function intToString(n: int): string
  requires n > 0
{
  intToStringHelper(n)
}

function concatenateIntegers(upperBound: int): string
  requires upperBound >= 1
  decreases upperBound
{
  if upperBound == 1 then "1"
  else concatenateIntegers(upperBound - 1) + intToString(upperBound)
}

predicate ValidInput(n: int)
{
  1 <= n <= 1000
}

predicate ValidOutput(n: int, result: string)
  requires ValidInput(n)
{
  var concatenatedString := concatenateIntegers(9999);
  if n <= |concatenatedString| then 
    |result| == 1 && result == [concatenatedString[n - 1]]
  else 
    result == ""
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
// </vc-code>
