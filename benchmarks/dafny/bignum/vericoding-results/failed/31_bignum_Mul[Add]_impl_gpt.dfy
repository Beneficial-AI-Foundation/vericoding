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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n/2) + (if n % 2 == 1 then "1" else "0")
}

lemma Lemma_Slice_Last_Append0(s: string)
  ensures (s + "0")[0..|s + "0"| - 1] == s
  ensures (s + "0")[|s + "0"| - 1] == '0'
{
  assert |s + "0"| == |s| + 1;
  assert (s + "0")[|s|] == '0';
  assert (s + "0")[0..|s + "0"| - 1] == s;
}

lemma Lemma_Slice_Last_Append1(s: string)
  ensures (s + "1")[0..|s + "1"| - 1] == s
  ensures (s + "1")[|s + "1"| - 1] == '1'
{
  assert |s + "1"| == |s| + 1;
  assert (s + "1")[|s|] == '1';
  assert (s + "1")[0..|s + "1"| - 1] == s;
}

lemma Lemma_Valid_Append0(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "0")
{
  assert forall i | 0 <= i < |s + "0"| ::
    (s + "0")[i] == '0' || (s + "0")[i] == '1' by {
      if i < |s| {
        assert (s + "0")[i] == s[i];
        assert s[i] == '0' || s[i] == '1';
      } else {
        assert i == |s|;
        assert (s + "0")[i] == '0';
      }
    };
}

lemma Lemma_Valid_Append1(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "1")
{
  assert forall i | 0 <= i < |s + "1"| ::
    (s + "1")[i] == '0' || (s + "1")[i] == '1' by {
      if i < |s| {
        assert (s + "1")[i] == s[i];
        assert s[i] == '0' || s[i] == '1';
      } else {
        assert i == |s|;
        assert (s + "1")[i] == '1';
      }
    };
}

lemma Lemma_Str2Int_Append0(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  Lemma_Slice_Last_Append0(s);
  assert |s + "0"| != 0;
  assert Str2Int(s + "0") ==
    2 * Str2Int((s + "0")[0..|s + "0"| - 1]) +
    (if (s + "0")[|s + "0"| - 1] == '1' then 1 else 0);
  assert (s + "0")[0..|s + "0"| - 1] == s;
  assert (s + "0")[|s + "0"| - 1] == '0';
  assert (if (s + "0")[|s + "0"| - 1] == '1' then 1 else 0) == 0;
}

lemma Lemma_Str2Int_Append1(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "1") == 2 * Str2Int(s) + 1
{
  Lemma_Slice_Last_Append1(s);
  assert |s + "1"| != 0;
  assert Str2Int(s + "1") ==
    2 * Str2Int((s + "1")[0..|s + "1"| - 1]) +
    (if (s + "1")[|s + "1"| - 1] == '1' then 1 else 0);
  assert (s + "
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n/2) + (if n % 2 == 1 then "1" else "0")
}

lemma Lemma_Slice_Last_Append0(s: string)
  ensures (s + "0")[0..|s + "0"| - 1] == s
  ensures (s + "0")[|s + "0"| - 1] == '0'
{
  assert |s + "0"| == |s| + 1;
  assert (s + "0")[|s|] == '0';
  assert (s + "0")[0..|s + "0"| - 1] == s;
}

lemma Lemma_Slice_Last_Append1(s: string)
  ensures (s + "1")[0..|s + "1"| - 1] == s
  ensures (s + "1")[|s + "1"| - 1] == '1'
{
  assert |s + "1"| == |s| + 1;
  assert (s + "1")[|s|] == '1';
  assert (s + "1")[0..|s + "1"| - 1] == s;
}

lemma Lemma_Valid_Append0(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "0")
{
  assert forall i | 0 <= i < |s + "0"| ::
    (s + "0")[i] == '0' || (s + "0")[i] == '1' by {
      if i < |s| {
        assert (s + "0")[i] == s[i];
        assert s[i] == '0' || s[i] == '1';
      } else {
        assert i == |s|;
        assert (s + "0")[i] == '0';
      }
    };
}

lemma Lemma_Valid_Append1(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "1")
{
  assert forall i | 0 <= i < |s + "1"| ::
    (s + "1")[i] == '0' || (s + "1")[i] == '1' by {
      if i < |s| {
        assert (s + "1")[i] == s[i];
        assert s[i] == '0' || s[i] == '1';
      } else {
        assert i == |s|;
        assert (s + "1")[i] == '1';
      }
    };
}

lemma Lemma_Str2Int_Append0(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  Lemma_Slice_Last_Append0(s);
  assert |s + "0"| != 0;
  assert Str2Int(s + "0") ==
    2 * Str2Int((s + "0")[0..|s + "0"| - 1]) +
    (if (s + "0")[|s + "0"| - 1] == '1' then 1 else 0);
  assert (s + "0")[0..|s + "0"| - 1] == s;
  assert (s + "0")[|s + "0"| - 1] == '0';
  assert (if (s + "0")[|s + "0"| - 1] == '1' then 1 else 0) == 0;
}

lemma Lemma_Str2Int_Append1(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "1") == 2 * Str2Int(s) + 1
{
  Lemma_Slice_Last_Append1(s);
  assert |s + "1"| != 0;
  assert Str2Int(s + "1") ==
    2 * Str2Int((s + "1")[0..|s + "1"| - 1]) +
    (if (s + "1")[|s + "1"| - 1] == '1' then 1 else 0);
  assert (s + "
// </vc-code>

