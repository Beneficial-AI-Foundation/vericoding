ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Str2Int_concat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(a + b)
  ensures Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    // trivial: a + "" = a
  } else {
    var bpre := b[0..|b|-1];
    var c := b[|b|-1];
    // By definition of Str2Int on (a + b):
    assert Str2Int(a + b) == 2 * Str2Int(a + bpre) + (if c == '1' then 1 else 0);
    // Apply inductive hypothesis to a + bpre
    Str2Int_concat(a, bpre);
    assert Str2Int(a + bpre) == pow2(|bpre|) * Str2Int(a) + Str2Int(bpre);
    // pow2 relation
    assert pow2(|b|) == 2 * pow2(|bpre|);
    // Str2Int relation for b
    assert Str2Int(b) == 2 * Str2Int(bpre) + (if c == '1' then 1 else 0);
    // Combine equalities
    assert Str2Int(a + b) == pow2(|b|) * Str2Int(a) + Str2Int(b);
  }
}
// </vc-helpers>

// <vc-spec>
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var i := |s1| - 1;
  var j := |s2| - 1;
  var res := "";
  var carry := 0;
  // Invariant: processed suffixes are s1[i+1..|s1|], s2[j+1..|s2|]
  while i >= 0 || j >= 0
    invariant 0 <= i + 1 <= |s1|
    invariant 0 <= j + 1 <= |s2|
    invariant 0 <= carry <= 1
    invariant ValidBitString(res)
    invariant Str2Int(res) + carry * pow2(|res|) == Str2Int(s1[i+1..|s1|]) + Str2Int(s2[j+1..|s2|])
  {
    var b1 := 0;
    if i >= 0 && s1[i] == '1' { b1 := 1; }
    var b2 := 0;
    if j >= 0 && s2[j] == '1' { b2 := 1; }
    var sum := b1 + b2 + carry;
    var digit := sum % 2;
    carry := sum / 2;
    if digit == 1 {
      res := "1" + res;
    } else {
      res := "0" + res;
    }
    i := i - 1;
    j := j - 1;
  }

  if carry == 1 {
    // prefix the remaining carry bit
    res := "1" + res;
    // use concat lemma to update numeric value:
    Str2Int_concat("1", res[1..|res|]); // proves relation for "1"+oldRes
  }

  // At this point, invariant with i = -1 and j = -1 yields:
  // Str2Int(res) == Str2Int(s1) + Str2Int(s2)
  // (if carry was 1 we prefixed it, so the above lemma ensures equality)
  return res;
}
// </vc-code>

