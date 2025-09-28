// <vc-preamble>
function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)

  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |x|
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < |result| ==> HasNoEvenDigit(result[j])
    invariant forall j, k :: 0 <= j < k < |result| ==> result[j] <= result[k]
    invariant forall e :: e in x[..i] && HasNoEvenDigit(e) ==> e in result
    invariant forall e :: e in result ==> e in x[..i]
  {
    if HasNoEvenDigit(x[i]) && x[i] !in result {
      var pos := 0;
      while pos < |result| && result[pos] < x[i]
        invariant 0 <= pos <= |result|
        invariant forall k :: 0 <= k < pos ==> result[k] < x[i]
      {
        pos := pos + 1;
      }
      result := result[..pos] + [x[i]] + result[pos..];
    }
  }
}
// </vc-code>
