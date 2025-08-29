function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma HasNoEvenDigitPreservesProperty(n: int)
  requires n >= 0
  ensures HasNoEvenDigit(n) ==> forall d :: d in Digits(n) ==> d % 2 == 1

function Digits(n: int): set<int>
  requires n >= 0
  decreases n
{
  if n < 10 then {n}
  else {n % 10} + Digits(n / 10)
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function SetToSortedSeq(s: set<int>): seq<int>
{
  if s == {} then []
  else 
    var min := SetMin(s);
    [min] + SetToSortedSeq(s - {min})
}

function SetMin(s: set<int>): int
  requires s != {}
{
  var x :| x in s;
  if forall y :: y in s ==> x <= y then x
  else SetMin(s - {x})
}

lemma SetToSortedSeqIsSorted(s: set<int>)
  ensures IsSorted(SetToSortedSeq(s))

lemma SetToSortedSeqComplete(s: set<int>)
  ensures forall x :: x in s <==> x in SetToSortedSeq(s)
// </vc-helpers>

// <vc-description>
/*
function_signature: def unique_digits(x: List[nat]) -> List[nat]
Given a list of positive integers x. return a sorted list of all elements that hasn't any even digit.
*/
// </vc-description>

// <vc-code>
method unique_digits(x: seq<int>) returns (result: seq<int>)
  requires forall i :: 0 <= i < |x| ==> x[i] >= 0
  ensures IsSorted(result)
  ensures forall y :: y in result ==> y >= 0 && HasNoEvenDigit(y) && y in x
  ensures forall y :: y in x && y >= 0 && HasNoEvenDigit(y) ==> y in result
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
  var filtered := {};
  var i := 0;
  
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall y :: y in filtered ==> y >= 0 && HasNoEvenDigit(y) && y in x[..i]
    invariant forall y :: y in x[..i] && y >= 0 && HasNoEvenDigit(y) ==> y in filtered
  {
    if HasNoEvenDigit(x[i]) {
      filtered := filtered + {x[i]};
    }
    i := i + 1;
  }
  
  result := SetToSortedSeq(filtered);
  SetToSortedSeqIsSorted(filtered);
  SetToSortedSeqComplete(filtered);
}
// </vc-code>
