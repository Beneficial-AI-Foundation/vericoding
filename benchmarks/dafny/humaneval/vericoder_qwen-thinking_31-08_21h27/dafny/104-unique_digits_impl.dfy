function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
predicate sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method InsertionSort(s: seq<int>) returns (res: seq<int>)
  ensures res == sorted(s)
  ensures |res| == |s|
{
  var res_local := [];
  for i := 0 to |s| - 1 {
    var j := |res_local|;
    while j > 0 && res_local[j-1] > s[i]
      invariant 0 <= j <= |res_local|
      invariant (forall k | 0 <= k < j-1 :: res_local[k] <= s[i])
      invariant (forall k | j-1 < k < |res_local| :: res_local[k] == res_local[k])
      invariant sorted(res_local[0..j])
    {
      j := j - 1;
    }
    res_local := res_local[0..j] + [s[i]] + res_local[j..|res_local|];
  }
  return res_local;
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
  var filtered := [e | e : x, HasNoEvenDigit(e)];
  return InsertionSort(filtered);
}
// </vc-code>

