function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma FilterPreservesProperty(s: seq<nat>, p: nat -> bool)
  ensures forall i :: 0 <= i < |filter(s, p)| ==> p(filter(s, p)[i])
{
  if |s| == 0 {
  } else {
    FilterPreservesProperty(s[1..], p);
  }
}

lemma FilterPreservesElements(s: seq<nat>, p: nat -> bool)
  ensures forall n :: n in filter(s, p) ==> n in s && p(n)
  ensures forall n :: n in s && p(n) ==> n in filter(s, p)
{
  if |s| == 0 {
  } else {
    FilterPreservesElements(s[1..], p);
  }
}

lemma SortedPreservesElements(s: seq<nat>)
  ensures multiset(s) == multiset(sort(s))
{
}

function filter(s: seq<nat>, p: nat -> bool): seq<nat>
{
  if |s| == 0 then [] else
    (if p(s[0]) then [s[0]] else []) + filter(s[1..], p)
}

function sort(s: seq<nat>): seq<nat>
  ensures |sort(s)| == |s|
  ensures multiset(s) == multiset(sort(s))
  ensures forall i, j :: 0 <= i < j < |sort(s)| ==> sort(s)[i] <= sort(s)[j]
{
  if |s| <= 1 then s
  else 
    var pivot := s[0];
    var rest := s[1..];
    var less := filter(rest, x => x < pivot);
    var greater := filter(rest, x => x >= pivot);
    sort(less) + [pivot] + sort(greater)
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
  requires forall i :: 0 <= i < |x| ==> x[i] >= 0
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall n :: n in result <==> n in x && HasNoEvenDigit(n)
// </vc-spec>
// <vc-code>
method unique_digits(x: seq<nat>) returns (result: seq<nat>)
  requires forall i :: 0 <= i < |x| ==> x[i] >= 0
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall n :: n in result <==> n in x && HasNoEvenDigit(n)
{
  var filtered := filter(x, HasNoEvenDigit);
  result := sort(filtered);
  FilterPreservesProperty(x, HasNoEvenDigit);
  FilterPreservesElements(x, HasNoEvenDigit);
  SortedPreservesElements(filtered);
}
// </vc-code>
