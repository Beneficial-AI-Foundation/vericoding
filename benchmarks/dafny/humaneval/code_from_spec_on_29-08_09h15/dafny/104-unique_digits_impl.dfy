function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma FilterPreservesProperty(s: seq<int>, filtered: seq<int>)
  requires forall i :: 0 <= i < |filtered| ==> filtered[i] in s && HasNoEvenDigit(filtered[i])
  ensures forall e :: e in filtered ==> e in s
{
}

lemma SortedSequenceProperty(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}

method FilterByDigits(x: seq<int>) returns (filtered: seq<int>)
  ensures forall i :: 0 <= i < |filtered| ==> HasNoEvenDigit(filtered[i])
  ensures forall e :: e in filtered ==> e in x
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in filtered
{
  filtered := [];
  for i := 0 to |x|
    invariant forall j :: 0 <= j < |filtered| ==> HasNoEvenDigit(filtered[j])
    invariant forall e :: e in filtered ==> e in x
    invariant forall j :: 0 <= j < i ==> (x[j] in filtered <==> HasNoEvenDigit(x[j]))
  {
    if HasNoEvenDigit(x[i]) {
      filtered := filtered + [x[i]];
    }
  }
}

method SortSequence(s: seq<int>) returns (sorted: seq<int>)
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall e :: e in s <==> e in sorted
{
  sorted := s;
  for i := 0 to |sorted|
    invariant multiset(s) == multiset(sorted)
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant forall e :: e in s <==> e in sorted
    invariant forall j, k :: 0 <= j < i && i <= k < |sorted| ==> sorted[j] <= sorted[k]
  {
    var minIdx := i;
    for j := i + 1 to |sorted|
      invariant i <= minIdx < |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
      invariant multiset(s) == multiset(sorted)
      invariant forall e :: e in s <==> e in sorted
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
    }
    if minIdx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIdx]][minIdx := temp];
    }
  }
}

lemma SortPreservesProperty(s: seq<int>, sorted: seq<int>)
  requires multiset(s) == multiset(sorted)
  requires forall i :: 0 <= i < |s| ==> HasNoEvenDigit(s[i])
  ensures forall i :: 0 <= i < |sorted| ==> HasNoEvenDigit(sorted[i])
{
  forall i | 0 <= i < |sorted|
    ensures HasNoEvenDigit(sorted[i])
  {
    assert sorted[i] in multiset(sorted);
    assert multiset(s) == multiset(sorted);
    assert sorted[i] in multiset(s);
    assert exists j :: 0 <= j < |s| && s[j] == sorted[i];
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
  var filtered := FilterByDigits(x);
  result := SortSequence(filtered);
  SortPreservesProperty(filtered, result);
}
// </vc-code>

