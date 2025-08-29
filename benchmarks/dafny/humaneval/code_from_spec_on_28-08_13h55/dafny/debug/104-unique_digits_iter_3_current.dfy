function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma HasNoEvenDigitPreservesProperty(n: int)
  requires n >= 0
  ensures HasNoEvenDigit(n) ==> forall d :: d in Digits(n) ==> d % 2 == 1
{
  if n < 10 {
    assert Digits(n) == {n};
  } else if HasNoEvenDigit(n) {
    assert n % 2 == 1;
    assert HasNoEvenDigit(n / 10);
    HasNoEvenDigitPreservesProperty(n / 10);
  }
}

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
  decreases s
{
  if s == {} then []
  else 
    var min := SetMin(s);
    [min] + SetToSortedSeq(s - {min})
}

function SetMin(s: set<int>): int
  requires s != {}
  ensures SetMin(s) in s
  ensures forall x :: x in s ==> SetMin(s) <= x
{
  var x :| x in s && forall y :: y in s ==> x <= y;
  x
}

lemma SetToSortedSeqIsSorted(s: set<int>)
  ensures IsSorted(SetToSortedSeq(s))
{
  if s == {} {
    assert IsSorted([]);
  } else {
    var min := SetMin(s);
    var rest := s - {min};
    SetToSortedSeqIsSorted(rest);
    var restSeq := SetToSortedSeq(rest);
    assert forall y :: y in rest ==> min <= y;
    
    forall i | 0 <= i < |restSeq|
      ensures min <= restSeq[i]
    {
      assert restSeq[i] in restSeq;
      SetToSortedSeqComplete(rest);
      assert restSeq[i] in rest;
      assert min <= restSeq[i];
    }
  }
}

lemma SetToSortedSeqComplete(s: set<int>)
  ensures forall x :: x in s <==> x in SetToSortedSeq(s)
{
  if s == {} {
    assert SetToSortedSeq(s) == [];
  } else {
    var min := SetMin(s);
    var rest := s - {min};
    SetToSortedSeqComplete(rest);
    var restSeq := SetToSortedSeq(rest);
    assert SetToSortedSeq(s) == [min] + restSeq;
  }
}

lemma SetToSortedSeqUnique(s: set<int>)
  ensures forall i, j :: 0 <= i < j < |SetToSortedSeq(s)| ==> SetToSortedSeq(s)[i] != SetToSortedSeq(s)[j]
{
  if s == {} {
    assert SetToSortedSeq(s) == [];
  } else {
    var min := SetMin(s);
    var rest := s - {min};
    SetToSortedSeqUnique(rest);
    SetToSortedSeqComplete(rest);
    var restSeq := SetToSortedSeq(rest);
    assert min !in rest;
    assert forall x :: x in restSeq ==> x in rest;
    assert forall x :: x in restSeq ==> x != min;
  }
}
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
  SetToSortedSeqUnique(filtered);
  
  assert x[..i] == x;
}
// </vc-code>
