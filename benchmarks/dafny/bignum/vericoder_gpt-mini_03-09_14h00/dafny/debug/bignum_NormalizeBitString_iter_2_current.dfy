ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
function pow2(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * pow2(k - 1)
}

lemma Pow2Succ(k: nat)
  ensures pow2(k + 1) == 2 * pow2(k)
{
  if k == 0 {
    assert pow2(1) == 2;
    assert pow2(0) == 1;
  } else {
    // Unfolding the definition of pow2 gives the desired equality
    assert pow2(k + 1) == 2 * pow2(k);
  }
}

lemma RemoveSingleLast(x: string, tail: string)
  requires |tail| == 1
  ensures (x + tail)[0..|x + tail| - 1] == x
{
  // |x + tail| = |x| + 1, so |x + tail| - 1 = |x|
  assert |x + tail| == |x| + 1;
  assert |x + tail| - 1 == |x|;
  assert (x + tail)[0..|x + tail| - 1]
// </vc-helpers>

// <vc-spec>
method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
// </vc-spec>
// <vc-code>
function pow2(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * pow2(k - 1)
}

lemma Pow2Succ(k: nat)
  ensures pow2(k + 1) == 2 * pow2(k)
{
  if k == 0 {
    assert pow2(1) == 2;
    assert pow2(0) == 1;
  } else {
    // Unfolding the definition of pow2 gives the desired equality
    assert pow2(k + 1) == 2 * pow2(k);
  }
}

lemma RemoveSingleLast(x: string, tail: string)
  requires |tail| == 1
  ensures (x + tail)[0..|x + tail| - 1] == x
{
  // |x + tail| = |x| + 1, so |x + tail| - 1 = |x|
  assert |x + tail| == |x| + 1;
  assert |x + tail| - 1 == |x|;
  assert (x + tail)[0..|x + tail| - 1]
// </vc-code>

