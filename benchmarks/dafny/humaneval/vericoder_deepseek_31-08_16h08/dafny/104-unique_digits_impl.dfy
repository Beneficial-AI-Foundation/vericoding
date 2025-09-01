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
  ensures e in set y | y in x && HasNoEvenDigit(y)
{
}

lemma FilterOnlyFromSource(x: seq<int>, e: int)
  requires e in set y | y in x && HasNoEvenDigit(y)
  ensures e in x && HasNoEvenDigit(e)
{
}

function sorted_copy(x: seq<int>) : seq<int>
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures multiset(x) == multiset(result)
{
  if |x| <= 1 then
    x
  else
    var mid := |x| / 2;
    var left := sorted_copy(x[..mid]);
    var right := sorted_copy(x[mid..]);
    merge(left, right)
}

function merge(a: seq<int>, b: seq<int>) : seq<int>
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < |b| ==> b[i] <= b[j]
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures multiset(result) == multiset(a) + multiset(b)
{
  if |a| == 0 then
    b
  else if |b| == 0 then
    a
  else if a[0] <= b[0] then
    [a[0]] + merge(a[1..], b)
  else
    [b[0]] + merge(a, b[1..])
}
// </vc-helpers>
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
  var filtered_set := set y | y in x where HasNoEvenDigit(y);
  var filtered_seq := [y | y in filtered_set];
  var sorted := sorted_copy(filtered_seq);
  result := sorted;
}
// </vc-code>

