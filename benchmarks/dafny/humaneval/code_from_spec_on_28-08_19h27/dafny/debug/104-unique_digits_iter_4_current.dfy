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

lemma FilterHasNoEvenDigitCorrectness(x: seq<nat>)
  requires forall i :: 0 <= i < |x| ==> x[i] > 0
  ensures forall n :: n in FilterHasNoEvenDigit(x) ==> n in x && HasNoEvenDigit(n)
  ensures forall n :: n in x && HasNoEvenDigit(n) ==> n in FilterHasNoEvenDigit(x)
  ensures forall i :: 0 <= i < |FilterHasNoEvenDigit(x)| ==> FilterHasNoEvenDigit(x)[i] > 0 && HasNoEvenDigit(FilterHasNoEvenDigit(x)[i])
{
  if |x| == 0 {
    // Base case
  } else {
    // Inductive case
    FilterHasNoEvenDigitCorrectness(x[1..]);
    if HasNoEvenDigit(x[0]) {
      // x[0] is included in the result
    } else {
      // x[0] is not included in the result
    }
  }
}

method SortSeq(x: seq<nat>) returns (result: seq<nat>)
  ensures multiset(result) == multiset(x)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
  result := x;
  var i := 0;
  while i < |result|
    invariant 0 <= i <= |result|
    invariant multiset(result) == multiset(x)
    invariant forall p, q :: 0 <= p < q < i ==> result[p] <= result[q]
  {
    var j := i + 1;
    while j < |result|
      invariant i < j <= |result|
      invariant multiset(result) == multiset(x)
      invariant forall p, q :: 0 <= p < q < i ==> result[p] <= result[q]
      invariant forall k :: i < k < j ==> result[i] <= result[k]
    {
      if result[j] < result[i] {
        result := result[i := result[j]][j := result[i]];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
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
  FilterHasNoEvenDigitCorrectness(x);
  result := SortSeq(filtered);
}
// </vc-code>
