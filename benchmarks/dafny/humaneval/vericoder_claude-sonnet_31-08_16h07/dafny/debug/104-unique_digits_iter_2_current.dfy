function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma HasNoEvenDigitCorrect(n: int)
  requires n >= 0
  ensures HasNoEvenDigit(n) <==> (forall d :: d in DigitsOf(n) ==> d % 2 == 1)
{
  if n < 10 {
    assert DigitsOf(n) == [n];
    assert HasNoEvenDigit(n) == (n % 2 == 1);
    assert forall d :: d in DigitsOf(n) ==> d % 2 == 1 <==> n % 2 == 1;
  } else {
    HasNoEvenDigitCorrect(n / 10);
    assert DigitsOf(n) == DigitsOf(n / 10) + [n % 10];
    assert HasNoEvenDigit(n) == (n % 2 == 1 && HasNoEvenDigit(n / 10));
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
  decreases |s|
{
  if |s| <= 1 then s
  else 
    var pivot := s[0];
    var smaller := Filter(s[1..], x => x <= pivot);
    var larger := Filter(s[1..], x => x > pivot);
    Sort(smaller) + [pivot] + Sort(larger)
}

lemma FilterSizeProperty<T>(s: seq<T>, p: T -> bool)
  ensures |Filter(s, p)| <= |s|
{
  if |s| == 0 {
  } else {
    FilterSizeProperty(s[1..], p);
  }
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
  decreases |s|
{
  if |s| <= 1 {
  } else {
    var pivot := s[0];
    var smaller := Filter(s[1..], x => x <= pivot);
    var larger := Filter(s[1..], x => x > pivot);
    FilterPreservesProperty(s[1..], x => x <= pivot);
    FilterPreservesProperty(s[1..], x => x > pivot);
    FilterSizeProperty(s[1..], x => x <= pivot);
    FilterSizeProperty(s[1..], x => x > pivot);
    SortPreservesElements(smaller);
    SortPreservesElements(larger);
    assert |smaller| + |larger| == |s[1..]|;
    assert |Sort(s)| == |Sort(smaller)| + 1 + |Sort(larger)|;
    assert |Sort(s)| == |smaller| + 1 + |larger|;
    assert |Sort(s)| == |s[1..]| + 1;
    assert |Sort(s)| == |s|;
  }
}

lemma SortIsSorted(s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |Sort(s)| ==> Sort(s)[i] <= Sort(s)[j]
  decreases |s|
{
  if |s| <= 1 {
  } else {
    var pivot := s[0];
    var smaller := Filter(s[1..], x => x <= pivot);
    var larger := Filter(s[1..], x => x > pivot);
    FilterSizeProperty(s[1..], x => x <= pivot);
    FilterSizeProperty(s[1..], x => x > pivot);
    SortIsSorted(smaller);
    SortIsSorted(larger);
    FilterPreservesProperty(s[1..], x => x <= pivot);
    FilterPreservesProperty(s[1..], x => x > pivot);
    SortPreservesElements(smaller);
    SortPreservesElements(larger);
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
  
  forall i | 0 <= i < |result|
    ensures HasNoEvenDigit(result[i])
  {
    assert result[i] in filtered;
    HasNoEvenDigitCorrect(result[i]);
  }
}
// </vc-code>

