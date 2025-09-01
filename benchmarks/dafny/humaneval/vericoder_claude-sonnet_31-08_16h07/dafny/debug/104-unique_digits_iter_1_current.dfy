function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma HasNoEvenDigitPreserved(n: int)
  requires n >= 0
  ensures HasNoEvenDigit(n) <==> (forall d :: d in DigitsOf(n) ==> d % 2 == 1)
{
  if n < 10 {
    assert DigitsOf(n) == [n];
  } else {
    HasNoEvenDigitPreserved(n / 10);
  }
}

function DigitsOf(n: int): seq<int>
  requires n >= 0
  decreases n
{
  if n < 10 then [n] else DigitsOf(n / 10) + [n % 10]
}

function Filter<T>(s: seq<T>, p: T -> bool): seq<T>
{
  if |s| == 0 then []
  else if p(s[0]) then [s[0]] + Filter(s[1..], p)
  else Filter(s[1..], p)
}

function Sort(s: seq<int>): seq<int>
{
  if |s| <= 1 then s
  else 
    var pivot := s[0];
    var smaller := Filter(s[1..], x => x <= pivot);
    var larger := Filter(s[1..], x => x > pivot);
    Sort(smaller) + [pivot] + Sort(larger)
}

lemma FilterPreservesProperty<T>(s: seq<T>, p: T -> bool)
  ensures forall x :: x in Filter(s, p) ==> p(x)
  ensures forall x :: x in Filter(s, p) ==> x in s
  ensures forall x :: x in s && p(x) ==> x in Filter(s, p)
{
  if |s| == 0 {
  } else {
    FilterPreservesProperty(s[1..], p);
  }
}

lemma SortPreservesElements(s: seq<int>)
  ensures forall x :: x in Sort(s) <==> x in s
  ensures |Sort(s)| == |s|
{
  if |s| <= 1 {
  } else {
    var pivot := s[0];
    var smaller := Filter(s[1..], x => x <= pivot);
    var larger := Filter(s[1..], x => x > pivot);
    FilterPreservesProperty(s[1..], x => x <= pivot);
    FilterPreservesProperty(s[1..], x => x > pivot);
    SortPreservesElements(smaller);
    SortPreservesElements(larger);
  }
}

lemma SortIsSorted(s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |Sort(s)| ==> Sort(s)[i] <= Sort(s)[j]
{
  if |s| <= 1 {
  } else {
    var pivot := s[0];
    var smaller := Filter(s[1..], x => x <= pivot);
    var larger := Filter(s[1..], x => x > pivot);
    SortIsSorted(smaller);
    SortIsSorted(larger);
    FilterPreservesProperty(s[1..], x => x <= pivot);
    FilterPreservesProperty(s[1..], x => x > pivot);
  }
}
// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var filtered := Filter(x, HasNoEvenDigit);
  result := Sort(filtered);
  
  FilterPreservesProperty(x, HasNoEvenDigit);
  SortPreservesElements(filtered);
  SortIsSorted(filtered);
}
// </vc-code>

