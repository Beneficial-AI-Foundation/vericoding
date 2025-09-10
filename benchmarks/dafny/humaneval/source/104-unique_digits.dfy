function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}
// pure-end
method UniqueDigits(x: seq<int>) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
  // post-conditions-end
{
  // impl-start
  result := [];

  for i := 0 to |x|
    // invariants-start
    invariant forall j :: 0 <= j < |result| ==> HasNoEvenDigit(result[j])
    invariant forall e :: e in result ==> e in x[..i]
    invariant forall e :: e in x[..i] && HasNoEvenDigit(e) ==> e in result
    // invariants-end
  {
    if HasNoEvenDigit(x[i]) {
      result := result + [x[i]];
    }
  }

  ghost var unsorted := result;

  var i := 0;
  while i < |result|
    // invariants-start
    invariant 0 <= i <= |result|
    invariant forall j, k :: 0 <= j < k < i ==> result[j] <= result[k]
    invariant multiset(unsorted) == multiset(result)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |result| ==> result[j] <= result[k]
    invariant forall e :: e in result ==> HasNoEvenDigit(e)
    invariant forall e :: e in result ==> e in x
    // invariants-end
  {
    var minIndex := i;
    var j := i + 1;
    while j < |result|
      // invariants-start
      invariant i <= minIndex < j <= |result|
      invariant forall k :: i <= k < j ==> result[minIndex] <= result[k]
      // invariants-end
    {
      if result[j] < result[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := result[i];
      result := result[i := result[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }

  assert forall e :: e in result ==> HasNoEvenDigit(e); // assert-line
  assert forall e :: e in result ==> e in x; // assert-line
  // assert-start
  assert forall e :: e in x && HasNoEvenDigit(e) ==> e in result by {
    assert forall e :: e in unsorted ==> e in multiset(result);
  }
  // assert-end
  // impl-end
}
