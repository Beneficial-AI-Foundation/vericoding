```vc-helpers
function Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma SubstringValid(s: string, i: int, j: int)
  requires ValidBitString(s)
  requires 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
{
  // Follows from the definition of ValidBitString (forall over indices).
}

lemma ConcatPrefix(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures (a + b)[0..|a|] == a
{
  // For each index within a, the concatenation (a+b) equals a at that index.
  forall k | 0 <= k < |a|
    ensures (a + b)[k] == a[k]
  {
    // The semantics of string concatenation yields this equality.
  }
  // Length of the slice (a+b)[0..|a|] is |a| by definition of slice, so the slices are equal.
}

lemma StrSliceLastIsLastChar(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  requires |b| > 0
  ensures (a + b)[|a|] == b[0]
{
  // By definition of concatenation, the character at position |a| of (a+b) is b[0].
}

method ToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  n := 0;
  var i := 0;
  SubstringValid(s, 0, 0);
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
    invariant ValidBitString(s[0..i])
    decreases |s| - i
  {
    var bit := (if s[i] == '1' then 1 else 0);
    var newn := n * 2 + bit;
    // Prove newn equals Str2Int(s[0..i+1])
    SubstringValid(s, i, i + 1);
    StrConcatLemma(s[0..i], s[i..i+1]);
    SingleCharStrVal(s, i);
    // From StrConcatLemma and SingleCharStrVal we obtain:
    // Str2Int(s[0..i+1]) == Str2Int(s[0..i]) * Exp_int(2,1) + Str2Int(s[i..i+1])
    // Exp_int(2,1) == 2 and Str2Int(s[i..i+1]) == bit, so newn == Str2Int(s[0..i+1]).
    n := newn;
    i := i + 1;
    SubstringValid(s, 0, i);
  }
}

lemma ExpAdd(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
  } else {
    ExpAdd(x, a, b - 1);
  }
}

lemma Exp2_mult(n: nat)
  ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
{
  ExpAdd(2, n, 1);
}

lemma StrConcatLemma(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * Exp_int(2, |b|) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    // trivial: a + "" = a, Exp_int(2,0) = 1, Str2Int("") = 0
  } else if |b| == 1 {
    // Use definition of Str2Int on a+b whose last character is b[0].
    // (a + b)[0..|a+b|-1] = (a + b)[0..|a|] = a
    ConcatPrefix(a, b);
    SingleCharStrVal(b, 0);
    Exp2_mult(0); // Exp_int(2,1) == 2 * Exp_int(2,0) == 2
    // By definition of Str2Int:
    // Str2Int(a + b) == 2 * Str2Int((a+b)[0..|a+b|-1]) + Str2Int(b)
    // and (a+b)[0..|a+b|-1] == a, so get desired equality.
  } else {
    var bprefix := b[0..|b|-1];
    var last := b[|b|-1..|b|];
    // Inductive hypothesis on shorter suffixes
    StrConcatLemma(a, bprefix);
    StrConcatLemma(bprefix, last);
    // Relate powers of two
    Exp2_mult(|b| - 1);
    // Arithmetic follows from the recursive equalities above.
  }
}

lemma SingleCharStrVal(s