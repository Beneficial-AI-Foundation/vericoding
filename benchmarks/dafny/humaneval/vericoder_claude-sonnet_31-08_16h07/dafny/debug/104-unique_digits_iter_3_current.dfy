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
  } else {
    HasNoEvenDigitCorrect(n / 10);
    assert DigitsOf(n) == DigitsOf(n / 10) + [n % 10];
    assert HasNoEvenDigit(n) == ((n % 10) % 2 == 1 && HasNoEvenDigit(n / 10));
    assert (n % 10) % 2 == 1 <==> (n % 2 == 1);
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

lemma FilterPartition<T>(s: seq<T>, p: T -> bool)
  ensures |Filter(s, p)| + |Filter(s, x => !p(x))| == |s|
{
  if |s| == 0 {
  } else {
    FilterPartition(s[1..], p);
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
    FilterPartition(s[1..], x => x <= pivot);
    assert |smaller| + |larger| == |s[1..]|;
    SortPreservesElements(smaller);
    SortPreservesElements(larger);
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
    var sorted := Sort(smaller) + [pivot] + Sort(larger);
    
    FilterSizeProperty(s[1..], x => x <= pivot);
    FilterSizeProperty(s[1..], x => x > pivot);
    SortIsSorted(smaller);
    SortIsSorted(larger);
    FilterPreservesProperty(s[1..], x => x <= pivot);
    FilterPreservesProperty(s[1..], x => x > pivot);
    SortPreservesElements(smaller);
    SortPreservesElements(larger);
    
    forall i, j | 0 <= i < j < |sorted|
      ensures sorted[i] <= sorted[j]
    {
      var smallerLen := |Sort(smaller)|;
      var pivotIdx := smallerLen;
      var largerStart := smallerLen + 1;
      
      if i < smallerLen && j < smallerLen {
        assert sorted[i] == Sort(smaller)[i];
        assert sorted[j] == Sort(smaller)[j];
      } else if i < smallerLen && j == pivotIdx {
        assert sorted[i] in Sort(smaller);
        assert Sort(smaller)[i] in smaller;
        assert smaller[i] <= pivot;
      } else if i < smallerLen && j >= largerStart {
        assert sorted[i] in Sort(smaller);
        assert sorted[j] in Sort(larger);
        assert Sort(smaller)[i] in smaller;
        assert Sort(larger)[j - largerStart] in larger;
        assert smaller[i] <= pivot;
        assert larger[j - largerStart] > pivot;
      } else if i == pivotIdx && j >= largerStart {
        assert sorted[i] == pivot;
        assert sorted[j] in Sort(larger);
        assert Sort(larger)[j - largerStart] in larger;
        assert larger[j - largerStart] > pivot;
      } else if i >= largerStart && j >= largerStart {
        assert sorted[i] == Sort(larger)[i - largerStart];
        assert sorted[j] == Sort(larger)[j - largerStart];
      }
    }
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
  }
}
// </vc-code>

