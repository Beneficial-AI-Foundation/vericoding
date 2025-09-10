predicate ValidInput(y: int)
{
    1000 <= y <= 9000
}

function HasDistinctDigits(n: int): bool
{
    var digits := NumberToDigits(n);
    AllDistinct(digits)
}

function NumberToDigits(n: int): seq<int>
{
    if n == 0 then [0]
    else if n > 0 then NumberToDigitsHelper(n, [])
    else NumberToDigitsHelper(-n, [])
}

function NumberToDigitsHelper(n: int, acc: seq<int>): seq<int>
requires n >= 0
decreases n
{
    if n == 0 then acc
    else NumberToDigitsHelper(n / 10, [n % 10] + acc)
}

predicate AllDistinct(digits: seq<int>)
{
    forall i, j :: 0 <= i < j < |digits| ==> digits[i] != digits[j]
}

// <vc-helpers>
function NextNumberWithDistinctDigits(n: int): int
  requires n >= 0
{
  var current := n + 1;
  while !HasDistinctDigits(current)
    invariant current >= n + 1
  {
    current := current + 1;
  }
  return current;
}
// </vc-helpers>

// <vc-spec>
method solve(y: int) returns (result: int)
requires ValidInput(y)
ensures result > y
ensures HasDistinctDigits(result)
ensures forall n :: y < n < result ==> !HasDistinctDigits(n)
// </vc-spec>
// <vc-code>
{
  result := NextNumberWithDistinctDigits(y);
}
// </vc-code>

