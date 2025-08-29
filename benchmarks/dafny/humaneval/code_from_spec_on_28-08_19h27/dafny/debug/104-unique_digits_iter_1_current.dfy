function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma HasNoEvenDigitPreservation(n: int)
  requires n > 0
  ensures HasNoEvenDigit(n) <==> (n % 2 == 1 && (n < 10 || HasNoEvenDigit(n / 10)))
{
}

function FilterHasNoEvenDigit(x: seq<nat>) : seq<nat>
{
  if |x| == 0 then []
  else if HasNoEvenDigit(x[0]) then [x[0]] + FilterHasNoEvenDigit(x[1..])
  else FilterHasNoEvenDigit(x[1..])
}

method SortSeq(x: seq<nat>) returns (result: seq<nat>)
  ensures multiset(result) == multiset(x)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
// </vc-helpers>

// <vc-description>
/*
function_signature: def unique_digits(x: List[nat]) -> List[nat]
Given a list of positive integers x. return a sorted list of all elements that hasn't any even digit.
*/
// </vc-description>

// <vc-spec>
method unique_digits(x: seq<nat>) returns (result: seq<nat>)
  requires forall i :: 0 <= i < |x| ==> x[i] > 0
  ensures forall i :: 0 <= i < |result| ==> result[i] > 0 && HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall n :: n in result ==> n in x && HasNoEvenDigit(n)
  ensures forall n :: n in x && HasNoEvenDigit(n) ==> n in result
// </vc-spec>
// <vc-code>
{
  var filtered := FilterHasNoEvenDigit(x);
  result := SortSeq(filtered);
}
// </vc-code>
