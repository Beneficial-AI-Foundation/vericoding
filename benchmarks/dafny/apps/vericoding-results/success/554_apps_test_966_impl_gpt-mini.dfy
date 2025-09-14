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
lemma NextDistinctExists(y: int)
requires ValidInput(y)
ensures exists k :: y < k < 10000 && HasDistinctDigits(k)
{
  // Witness 9012 satisfies the property.
  assert y <= 9000;
  assert y < 9012;
  assert 9012 < 10000;
  assert HasDistinctDigits(9012);
  assert exists k :: y < k < 10000 && HasDistinctDigits(k);
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
  var n := y + 1;
  while n < 10000 && !HasDistinctDigits(n)
    invariant y < n && n <= 10000
    invariant forall k :: y < k < n ==> !HasDistinctDigits(k)
    decreases 10000 - n
  {
    n := n + 1;
  }
  if n == 10000 {
    // Use the witness 9012 to derive a contradiction with the loop invariant.
    assert y <= 9000;
    assert y < 9012;
    assert HasDistinctDigits(9012);
    assert forall k :: y < k < n ==> !HasDistinctDigits(k);
    assert y < 9012 && 9012 < n;
    assert !HasDistinctDigits(9012);
    assert false;
  }
  assert n < 10000;
  assert HasDistinctDigits(n);
  result := n;
}
// </vc-code>

