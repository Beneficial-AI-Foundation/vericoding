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
  var digits := NumberToDigits(n);
  if HasDistinctDigits(n) {
    assert CountDistinctDigits(n) == |digits|;
  } else {
    assert CountDistinctDigits(n) < |digits|;
  }
}

function Log10(n: int): int
  requires n >= 0
  decreases n
{
  if n < 10 then 1
  else 1 + Log10(n / 10)
}

lemma NumberToDigitsLength(n: int)
  requires n >= 0
  ensures |NumberToDigits(n)| == (if n == 0 then 1 else Log10(n))
{
  if n == 0 {
  } else {
    calc {
      |NumberToDigits(n)|;
      == |NumberToDigitsHelper(n, [])|;
      == 
      { 
        var m := n;
        while m > 0 
          invariant m >= 0
          decreases m
        {
          m := m / 10;
        }
      }
      1 + Log10(n/10);
    }
  }
}

lemma NextDistinctExists(y: int)
  requires ValidInput(y)
  ensures exists n :: n > y && HasDistinctDigits(n)
{
  var candidate := y + 1;
  while candidate <= 9000 && !HasDistinctDigits(candidate)
    invariant candidate > y
    decreases 9001 - candidate
  {
    candidate := candidate + 1;
  }
  if candidate <= 9000 {
    assert HasDistinctDigits(candidate);
  } else {
    assert HasDistinctDigits(9012);
  }
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
  while !HasDistinctDigits(result) && result <= 9000
    invariant y < result <= 9001
    invariant forall n :: y < n < result ==> !HasDistinctDigits(n)
    decreases 9001 - result
  {
    result := result + 1;
  }
  if result > 9000 {
    result := 9012;
    assert HasDistinctDigits(9012);
  }
}
// </vc-code>

