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
lemma HasDistinctDigits_9876()
  ensures HasDistinctDigits(9876)
{
  assert NumberToDigits(9876) == NumberToDigitsHelper(9876, []);
  assert NumberToDigitsHelper(9876, []) == NumberToDigitsHelper(987, [6]);
  assert NumberToDigitsHelper(987, [6]) == NumberToDigitsHelper(98, [7, 6]);
  assert NumberToDigitsHelper(98, [7, 6]) == NumberToDigitsHelper(9, [8, 7, 6]);
  assert NumberToDigitsHelper(9, [8, 7, 6]) == NumberToDigitsHelper(0, [9, 8, 7, 6]);
  assert NumberToDigitsHelper(0, [9, 8, 7, 6]) == [9, 8, 7, 6];
  assert NumberToDigits(9876) == [9, 8, 7, 6];
  assert AllDistinct([9, 8, 7, 6]); // Verifiable by case analysis
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
  HasDistinctDigits_9876();
  ghost var z :| z > y && HasDistinctDigits(z);
  
  result := y + 1;
  while !HasDistinctDigits(result)
    invariant result > y
    invariant forall n :: y < n < result ==> !HasDistinctDigits(n)
    invariant result <= z
    decreases z - result
  {
    result := result + 1;
  }
}
// </vc-code>

