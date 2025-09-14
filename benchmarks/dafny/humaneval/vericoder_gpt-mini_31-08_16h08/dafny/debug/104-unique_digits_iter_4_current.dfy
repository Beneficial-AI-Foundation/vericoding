function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
lemma InsertPreserves(s: seq<int>, p: int, y: int, snew: seq<int>)
  requires 0 <= p <= |s|
  requires snew == s[..p] + [y] + s[p..]
  ensures forall v :: v in s ==> v in snew
  ensures y in snew
{
  // Prove every element of s is in snew
  forall v | v in s {
    if v in s[..p] {
      assert v in s[..p] + [y] + s[p..];
    } else {
      // then v must be in s[p..]
      assert v in s[p..];
      assert v in s[..p] + [y] + s[p..];
    }
  }
  // y is explicitly in the middle part
  assert y in s[..p] + [y] + s[p..];
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
    invariant forall m :: 0 <= m < j ==> cand[m] in s
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
    {
      p := p + 1;
    }
    // preserve old s elements via lemma
    ghost var olds := s;
    s := olds[..p] + [y] + olds[p..];
    InsertPreserves(olds, p, y, s);
    // now s contains all previous elements and y; the other invariants follow:
    // - every element of s is from cand: olds elements were from cand, y is cand[j]
    // - sortedness is preserved by insertion (by construction)
    j := j + 1;
  }

  // Remove duplicates from sorted sequence s to produce result in non-decreasing order
  var res: seq<int> := [];
  ghost var idxs: seq<int> := [];
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant |idxs| == |res|
    invariant forall t :: 0 <= t < |idxs| ==> 0 <= idxs[t] < k
    invariant forall p, q :: 0 <= p < q < |idxs| ==> idxs[p] < idxs[q]
    invariant forall t :: 0 <= t < |res| ==> res[t] == s[idxs[t]]
    invariant forall t :: 0 <= t < k ==> s[t] in res
    invariant forall v :: v in res ==> v in s
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] <= res[q]
    invariant forall v :: v in res ==> HasNoEvenDigit(v)
  {
    if k == 0 || s[k] != s[k-1] {
      res := res + [s[k]];
      idxs := idxs + [k];
    } else {
      // s[k] equals s[k-1], and by invariant s[k-1] in res, so s[k] is already in res
      assert s[k-1] in res;
      assert s[k] in res;
    }
    k := k + 1;
  }

  result := res;
}
// </vc-code>

