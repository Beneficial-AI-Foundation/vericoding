function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
function HasNoEvenDigit(n: int) : bool
  decreases if n < 0 then 0 else n
{
  if n < 0 then false
  else if n < 10 then n % 2 == 1
  else n % 2 == 1 && HasNoEvenDigit(n / 10)
}

method InsertionSort(lst: seq<int>) returns (result: seq<int>)
  ensures |result| == |lst|
  ensures forall i :: 0 <= i < |result| ==> result[i] in lst
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in lst ==> e in result

{
  result := [];
  for k := 0 to |lst|
  {
    result := InsertInOrder(result, lst[k]);
  }
}

method InsertInOrder(lst: seq<int>, x: int) returns (result: seq<int>)
  ensures |result| == |lst| + 1
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures multiset(result) == multiset(lst) + multiset{x}

{
  var i := 0;
  while (i < |lst| && lst[i] < x)
  {
    i := i + 1;
  }
  result := lst[..i] + [x] + lst[i..];
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
  var candidates : seq<int> := [];
  for i := 0 to |x|
  {
    if HasNoEvenDigit(x[i]) && x[i] !in candidates
    {
      candidates := candidates + [x[i]];
    }
  }
  result := InsertionSort(candidates);
}
// </vc-code>

