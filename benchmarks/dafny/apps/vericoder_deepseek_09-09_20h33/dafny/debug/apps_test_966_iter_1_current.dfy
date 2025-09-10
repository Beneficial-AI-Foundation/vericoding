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
lemma NumberToDigitsHelperCorrect(n: int, acc: seq<int>)
  requires n >= 0
  ensures NumberToDigitsHelper(n, acc) == NumberToDigitsHelper(n, []) + acc
  decreases n
{
  if n != 0 {
    NumberToDigitsHelperCorrect(n / 10, [n % 10] + acc);
  }
}

lemma NumberToDigitsPositive(n: int)
  requires n > 0
  ensures NumberToDigits(n) == NumberToDigitsHelper(n, [])
{
}

lemma DistinctHelper(digits: seq<int>)
  ensures AllDistinct(digits) <==> (forall i :: 0 <= i < |digits| ==> digits[i] !in digits[0..i])
{
}

function CountDistinctDigits(n: int): nat
{
  |set d | d in NumberToDigits(n)|
}

lemma DistinctImpliesCount(n: int)
  ensures HasDistinctDigits(n) <==> CountDistinctDigits(n) == |NumberToDigits(n)|
{
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
  result := y + 1;
  while !HasDistinctDigits(result)
    invariant result > y
    invariant forall n :: y < n < result ==> !HasDistinctDigits(n)
  {
    result := result + 1;
  }
}
// </vc-code>

