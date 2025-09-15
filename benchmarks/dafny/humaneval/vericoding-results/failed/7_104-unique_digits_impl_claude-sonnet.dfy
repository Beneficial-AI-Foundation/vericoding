// <vc-preamble>
function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed size preservation lemma and added helper lemmas for sorting verification */
predicate InSequence(e: int, s: seq<int>) {
  exists i :: 0 <= i < |s| && s[i] == e
}

function FilterNoEvenDigits(s: seq<int>): seq<int>
  decreases |s|
  ensures forall e :: e in FilterNoEvenDigits(s) ==> HasNoEvenDigit(e)
  ensures forall e :: e in FilterNoEvenDigits(s) ==> e in s
  ensures forall e :: e in s && HasNoEvenDigit(e) ==> e in FilterNoEvenDigits(s)
{
  if |s| == 0 then []
  else if HasNoEvenDigit(s[0]) then [s[0]] + FilterNoEvenDigits(s[1..])
  else FilterNoEvenDigits(s[1..])
}

function FilterSmaller(s: seq<int>, pivot: int): seq<int>
  decreases |s|
  ensures forall e :: e in FilterSmaller(s, pivot) ==> e < pivot
  ensures forall e :: e in FilterSmaller(s, pivot) ==> e in s
  ensures forall e :: e in s && e < pivot ==> e in FilterSmaller(s, pivot)
  ensures |FilterSmaller(s, pivot)| <= |s|
{
  if |s| == 0 then []
  else if s[0] < pivot then [s[0]] + FilterSmaller(s[1..], pivot)
  else FilterSmaller(s[1..], pivot)
}

function FilterEqual(s: seq<int>, pivot: int): seq<int>
  decreases |s|
  ensures forall e :: e in FilterEqual(s, pivot) ==> e == pivot
  ensures forall e :: e in FilterEqual(s, pivot) ==> e in s
  ensures forall e :: e in s && e == pivot ==> e in FilterEqual(s, pivot)
{
  if |s| == 0 then []
  else if s[0] == pivot then [s[0]] + FilterEqual(s[1..], pivot)
  else FilterEqual(s[1..], pivot)
}

function FilterLarger(s: seq<int>, pivot: int): seq<int>
  decreases |s|
  ensures forall e :: e in FilterLarger(s, pivot) ==> e > pivot
  ensures forall e :: e in FilterLarger(s, pivot) ==> e in s
  ensures forall e :: e in s && e > pivot ==> e in FilterLarger(s, pivot)
  ensures |FilterLarger(s, pivot)| <= |s|
{
  if |s| == 0 then []
  else if s[0] > pivot then [s[0]] + FilterLarger(s[1..], pivot)
  else FilterLarger(s[1..], pivot)
}

lemma SizePreservationLemma(s: seq<int>, pivot: int)
  requires |s| >= 1
  ensures |FilterSmaller(s[1..], pivot)| + |FilterEqual(s, pivot)| + |FilterLarger(s[1..], pivot)| == |s|
{
  if s[0] < pivot {
    SizePreservationLemma2(s, pivot);
  } else if s[0] == pivot {
    SizePreservationLemma3(s, pivot);
  } else {
    SizePreservationLemma4(s, pivot);
  }
}

lemma SizePreservationLemma2(s: seq<int>, pivot: int)
  requires |s| >= 1 && s[0] < pivot
  ensures |FilterSmaller(s[1..], pivot)| + |FilterEqual(s, pivot)| + |FilterLarger(s[1..], pivot)| == |s|
{
  assert |FilterEqual(s, pivot)| == |FilterEqual(s[1..], pivot)|;
  if |s[1..]| == 0 {
    assert |FilterSmaller(s[1..], pivot)| == 0;
    assert |FilterLarger(s[1..], pivot)| == 0;
  } else {
    SizePreservationLemma(s[1..], pivot);
  }
}

lemma SizePreservationLemma3(s: seq<int>, pivot: int)
  requires |s| >= 1 && s[0] == pivot
  ensures |FilterSmaller(s[1..], pivot)| + |FilterEqual(s, pivot)| + |FilterLarger(s[1..], pivot)| == |s|
{
  assert |FilterEqual(s, pivot)| == 1 + |FilterEqual(s[1..], pivot)|;
  if |s[1..]| == 0 {
    assert |FilterSmaller(s[1..], pivot)| == 0;
    assert |FilterLarger(s[1..], pivot)| == 0;
  } else {
    SizePreservationLemma(s[1..], pivot);
  }
}

lemma SizePreservationLemma4(s: seq<int>, pivot: int)
  requires |s| >= 1 && s[0] > pivot
  ensures |FilterSmaller(s[1..], pivot)| + |FilterEqual(s, pivot)| + |FilterLarger(s[1..], pivot)| == |s|
{
  assert |FilterEqual(s, pivot)| == |FilterEqual(s[1..], pivot)|;
  if |s[1..]| == 0 {
    assert |FilterSmaller(s[1..], pivot)| == 0;
    assert |FilterLarger(s[1..], pivot)| == 0;
  } else {
    SizePreservationLemma(s[1..], pivot);
  }
}

lemma SortedConcatenationLemma(s1: seq<int>, s2: seq<int>, s3: seq<int>, pivot: int)
  requires forall e :: e in s1 ==> e < pivot
  requires forall e :: e in s2 ==> e == pivot
  requires forall e :: e in s3 ==> e > pivot
  requires forall i, j :: 0 <= i < j < |s1| ==> s1[i] <= s1[j]
  requires forall i, j :: 0 <= i < j < |s3| ==> s3[i] <= s3[j]
  ensures forall i, j :: 0 <= i < j < |s1 + s2 + s3| ==> (s1 + s2 + s3)[i] <= (s1 + s2 + s3)[j]
{
  var combined := s1 + s2 + s3;
  forall i, j | 0 <= i < j < |combined|
    ensures combined[i] <= combined[j]
  {
    if i < |s1| && j < |s1| {
      assert combined[i] == s1[i];
      assert combined[j] == s1[j];
    } else if i < |s1| && |s1| <= j < |s1| + |s2| {
      assert combined[i] == s1[i];
      assert combined[j] == s2[j - |s1|];
      assert s1[i] < pivot && s2[j - |s1|] == pivot;
    } else if i < |s1| && j >= |s1| + |s2| {
      assert combined[i] == s1[i];
      assert combined[j] == s3[j - |s1| - |s2|];
      assert s1[i] < pivot && s3[j - |s1| - |s2|] > pivot;
    } else if |s1| <= i < |s1| + |s2| && |s1| <= j < |s1| + |s2| {
      assert combined[i] == s2[i - |s1|];
      assert combined[j] == s2[j - |s1|];
    } else if |s1| <= i < |s1| + |s2| && j >= |s1| + |s2| {
      assert combined[i] == s2[i - |s1|];
      assert combined[j] == s3[j - |s1| - |s2|];
      assert s2[i - |s1|] == pivot && s3[j - |s1| - |s2|] > pivot;
    } else {
      assert i >= |s1| + |s2| && j >= |s1| + |s2|;
      assert combined[i] == s3[i - |s1| - |s2|];
      assert combined[j] == s3[j - |s1| - |s2|];
    }
  }
}

function SortSequence(s: seq<int>): seq<int>
  decreases |s|
  ensures |SortSequence(s)| == |s|
  ensures forall i, j :: 0 <= i < j < |SortSequence(s)| ==> SortSequence(s)[i] <= SortSequence(s)[j]
  ensures forall e :: e in s <==> e in SortSequence(s)
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var smaller := FilterSmaller(s[1..], pivot);
    var equal := FilterEqual(s, pivot);
    var larger := FilterLarger(s[1..], pivot);
    SizePreservationLemma(s, pivot);
    var sorted_smaller := SortSequence(smaller);
    var sorted_larger := SortSequence(larger);
    SortedConcatenationLemma(sorted_smaller, equal, sorted_larger, pivot);
    sorted_smaller + equal + sorted_larger
}
// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)

  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Using verified helper functions */
{
  var filtered := FilterNoEvenDigits(x);
  result := SortSequence(filtered);
}
// </vc-code>
