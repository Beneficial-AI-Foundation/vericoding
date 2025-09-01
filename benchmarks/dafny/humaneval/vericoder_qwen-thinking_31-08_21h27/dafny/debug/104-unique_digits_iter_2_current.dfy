function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
method InsertionSort(s: seq<int>) returns (res: seq<int>)
  ensures res == sorted(s)
  ensures |res| == |s|
{
  var res := [];
  for i := 0 to |s| - 1 {
    var j := |res|;
    while j > 0 && res[j-1] > s[i]
      invariant 0 <= j <= |res|
      invariant (forall k | 0 <= k < j-1 :: res[k] <= s[i])
      invariant (forall k | j-1 < k < |res| :: res[k] == res[k])
      invariant res[0..j] is sorted
    {
      j := j - 1;
    }
    res := res[0..j] + [s[i]] + res[j..|res|];
  }
  return res;
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
  var filtered := [e | e in x where HasNoEvenDigit(e)];
  return InsertionSort(filtered);
}
// </vc-code>

