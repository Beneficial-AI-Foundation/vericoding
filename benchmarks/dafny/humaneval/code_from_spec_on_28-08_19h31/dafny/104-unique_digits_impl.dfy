function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma SortedPreservesNoEvenDigit(s: seq<int>)
  ensures forall i :: 0 <= i < |s| ==> HasNoEvenDigit(s[i]) ==> HasNoEvenDigit(s[i])
{
}

lemma FilterPreservesMembership(s: seq<int>, filtered: seq<int>)
  ensures forall e :: e in filtered ==> e in s
{
}

lemma FilteredMembership(filtered: seq<int>, s: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires forall e :: e in filtered ==> e in s[..i]
  requires forall e :: e in s[..i] && HasNoEvenDigit(e) ==> e in filtered
  ensures forall e :: e in filtered ==> e in s
  ensures forall e :: e in s && HasNoEvenDigit(e) ==> e in filtered
{
  if i == |s| {
    assert s[..i] == s;
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
method UniqueDigitsImpl(x: seq<int>) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
{
  var filtered: seq<int> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall e :: e in filtered ==> HasNoEvenDigit(e)
    invariant forall e :: e in filtered ==> e in x[..i]
    invariant forall e :: e in x[..i] && HasNoEvenDigit(e) ==> e in filtered
  {
    if HasNoEvenDigit(x[i]) {
      filtered := filtered + [x[i]];
    }
    i := i + 1;
  }
  
  FilteredMembership(filtered, x, |x|);
  
  result := [];
  i := 0;
  while i < |filtered|
    invariant 0 <= i <= |filtered|
    invariant forall j :: 0 <= j < |result| ==> HasNoEvenDigit(result[j])
    invariant forall j, k :: 0 <= j < k < |result| ==> result[j] <= result[k]
    invariant forall e :: e in result ==> e in filtered[..i]
    invariant forall e :: e in filtered[..i] ==> exists k :: 0 <= k < |result| && result[k] == e || e in filtered[i..]
    invariant forall e :: e in filtered[i..] ==> e in filtered
  {
    if i < |filtered| {
      var min := filtered[i];
      var minIndex := i;
      var j := i + 1;
      while j < |filtered|
        invariant i <= j <= |filtered|
        invariant i <= minIndex < |filtered|
        invariant min == filtered[minIndex]
        invariant forall k :: i <= k < j ==> min <= filtered[k]
      {
        if filtered[j] < min {
          min := filtered[j];
          minIndex := j;
        }
        j := j + 1;
      }
      result := result + [min];
      if minIndex != i {
        filtered := filtered[..i] + filtered[i+1..minIndex] + [filtered[i]] + filtered[minIndex+1..];
      } else {
        filtered := filtered[..i] + filtered[i+1..];
      }
      i := i + 1;
    }
  }
}
// </vc-code>
