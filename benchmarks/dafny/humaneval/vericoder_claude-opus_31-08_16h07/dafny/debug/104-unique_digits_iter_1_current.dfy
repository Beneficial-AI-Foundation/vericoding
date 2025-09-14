function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma HasNoEvenDigitSmaller(n: int)
  requires n >= 10
  requires HasNoEvenDigit(n)
  ensures HasNoEvenDigit(n / 10)
{
}

method MergeSort(a: seq<int>) returns (sorted: seq<int>)
  ensures multiset(sorted) == multiset(a)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  if |a| <= 1 {
    return a;
  }
  
  var mid := |a| / 2;
  var left := a[..mid];
  var right := a[mid..];
  
  var sortedLeft := MergeSort(left);
  var sortedRight := MergeSort(right);
  
  sorted := Merge(sortedLeft, sortedRight);
}

method Merge(left: seq<int>, right: seq<int>) returns (merged: seq<int>)
  requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  ensures multiset(merged) == multiset(left) + multiset(right)
  ensures forall i, j :: 0 <= i < j < |merged| ==> merged[i] <= merged[j]
{
  merged := [];
  var i, j := 0, 0;
  
  while i < |left| && j < |right|
    invariant 0 <= i <= |left| && 0 <= j <= |right|
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
    invariant forall k, l :: 0 <= k < l < |merged| ==> merged[k] <= merged[l]
    invariant |merged| > 0 && i < |left| ==> merged[|merged|-1] <= left[i]
    invariant |merged| > 0 && j < |right| ==> merged[|merged|-1] <= right[j]
  {
    if left[i] <= right[j] {
      merged := merged + [left[i]];
      i := i + 1;
    } else {
      merged := merged + [right[j]];
      j := j + 1;
    }
  }
  
  while i < |left|
    invariant 0 <= i <= |left|
    invariant multiset(merged) == multiset(left[..i]) + multiset(right)
    invariant forall k, l :: 0 <= k < l < |merged| ==> merged[k] <= merged[l]
    invariant |merged| > 0 && i < |left| ==> merged[|merged|-1] <= left[i]
  {
    merged := merged + [left[i]];
    i := i + 1;
  }
  
  while j < |right|
    invariant 0 <= j <= |right|
    invariant multiset(merged) == multiset(left) + multiset(right[..j])
    invariant forall k, l :: 0 <= k < l < |merged| ==> merged[k] <= merged[l]
    invariant |merged| > 0 && j < |right| ==> merged[|merged|-1] <= right[j]
  {
    merged := merged + [right[j]];
    j := j + 1;
  }
}

method RemoveDuplicates(sorted: seq<int>) returns (unique: seq<int>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |unique| ==> unique[i] < unique[j]
  ensures forall e :: e in sorted ==> e in unique
  ensures forall e :: e in unique ==> e in sorted
{
  if |sorted| == 0 {
    return [];
  }
  
  unique := [sorted[0]];
  var i := 1;
  
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant |unique| >= 1
    invariant forall j, k :: 0 <= j < k < |unique| ==> unique[j] < unique[k]
    invariant forall e :: e in sorted[..i] ==> e in unique
    invariant forall e :: e in unique ==> e in sorted[..i]
    invariant unique[|unique|-1] <= sorted[i-1]
  {
    if sorted[i] != unique[|unique|-1] {
      unique := unique + [sorted[i]];
    }
    i := i + 1;
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
  var filtered := [];
  var i := 0;
  
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < |filtered| ==> HasNoEvenDigit(filtered[j])
    invariant forall e :: e in filtered ==> e in x[..i]
    invariant forall e :: e in x[..i] && HasNoEvenDigit(e) ==> e in filtered
  {
    if HasNoEvenDigit(x[i]) {
      filtered := filtered + [x[i]];
    }
    i := i + 1;
  }
  
  var sorted := MergeSort(filtered);
  result := RemoveDuplicates(sorted);
}
// </vc-code>

