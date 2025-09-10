function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
// No additional helpers required for verification in this example.
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
  // Build candidate sequence of all elements from x that satisfy HasNoEvenDigit
  var cand: seq<int> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall k :: 0 <= k < i && HasNoEvenDigit(x[k]) ==> x[k] in cand
    invariant forall v :: v in cand ==> v in x[..i]
    invariant forall v :: v in cand ==> HasNoEvenDigit(v)
  {
    if HasNoEvenDigit(x[i]) {
      cand := cand + [x[i]];
    }
    i := i + 1;
  }

  // Insert elements of cand into s in non-decreasing order (insertion sort style)
  var s: seq<int> := [];
  var j := 0;
  while j < |cand|
    invariant 0 <= j <= |cand|
    invariant forall v :: v in cand[..j] ==> v in s
    invariant forall v :: v in s ==> v in cand
    invariant forall p, q :: 0 <= p < q < |s| ==> s[p] <= s[q]
    invariant forall v :: v in s ==> HasNoEvenDigit(v)
  {
    var y := cand[j];
    // find insertion position p: first index k where s[k] > y, or |s| if none
    var p := 0;
    while p < |s| && s[p] <= y
      invariant 0 <= p <= |s|
      invariant forall k :: 0 <= k < p ==> s[k] <= y
      invariant forall k :: p <= k < |s| ==> !(s[k] <= y) ==> s[k] > y
    {
      p := p + 1;
    }
    s := s[..p] + [y] + s[p..];
    // preserve HasNoEvenDigit property
    j := j + 1;
  }

  // Remove duplicates from sorted sequence s to produce result in non-decreasing order
  var res: seq<int> := [];
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant forall v :: v in s[..k] ==> v in res
    invariant forall v :: v in res ==> v in s
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] <= res[q]
    invariant forall v :: v in res ==> HasNoEvenDigit(v)
  {
    if k == 0 || s[k] != s[k-1] {
      res := res + [s[k]];
    }
    k := k + 1;
  }

  result := res;
}
// </vc-code>

