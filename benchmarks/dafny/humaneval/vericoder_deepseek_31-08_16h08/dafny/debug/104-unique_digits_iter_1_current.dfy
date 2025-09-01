function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma SortedSeqConcat(a: seq<int>, b: seq<int>)
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < |b| ==> b[i] <= b[j]
  requires |a| > 0 && |b| > 0 ==> a[|a|-1] <= b[0]
  ensures forall i, j :: 0 <= i < j < |a| + |b| ==> (a + b)[i] <= (a + b)[j]
{
}

lemma SortedSeqContains(a: seq<int>, e: int)
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  requires e in a
  ensures exists i :: 0 <= i < |a| && a[i] == e
{
}

lemma FilterPreservesMembership(x: seq<int>, e: int)
  requires e in x && HasNoEvenDigit(e)
  ensures e in [y | y in x && HasNoEvenDigit(y)]
{
}

lemma FilterOnlyFromSource(x: seq<int>, e: int)
  requires e in [y | y in x && HasNoEvenDigit(y)]
  ensures e in x && HasNoEvenDigit(e)
{
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
  var filtered := [y | y in x && HasNoEvenDigit(y)];
  var sorted := sorted_copy(filtered);
  result := sorted;
}
// </vc-code>

