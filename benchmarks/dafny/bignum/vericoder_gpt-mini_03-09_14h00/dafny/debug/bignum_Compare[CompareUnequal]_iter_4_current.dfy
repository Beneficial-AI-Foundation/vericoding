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

method CompareUnequal(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ValidSubstring(s: string, i: int)
  requires ValidBitString(s) && 0 <= i <= |s|
  ensures ValidBitString(s[0..i])
{
  assert forall j | 0 <= j < i :: s[0..i][j] == '0' || s[0..i][j] == '1';
}

lemma Str2Int_Snoc(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
  // The equality follows directly from the definition of Str2Int.
  // Make the unfolding explicit so Dafny can use it.
  assert Str2Int(s) ==
    (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  // Since |s| > 0, the if collapses to the second branch.
  assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
}
// </vc-helpers>

// <vc-spec>
method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var n1: nat := 0;
  var i: nat := 0;
  ValidSubstring(s1, 0);
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant n1 == Str2Int(s1[0..i])
    decreases |s1| - i
  {
    var bit := if s1[i] == '1' then 1 else 0;
    ValidSubstring(s1, i + 1);
    n1 := 2 * n1 + bit;
    i := i + 1;
    Str2Int_Snoc(s1[0..i]);
    assert n1 == Str2Int(s1[0..i]);
  }

  var n2: nat := 0;
  i := 0;
  ValidSubstring(s2, 0);
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant n2 == Str2Int(s2[0..i])
    decreases |s2| - i
  {
    var bit := if s2[i] == '1' then 1 else 0;
    ValidSubstring(s2, i + 1);
    n2 := 2 * n2 + bit;
    i := i + 1;
    Str2Int_Snoc(s2[0..i]);
    assert n2 == Str2Int(s2[0..i]);
  }

  assert n1 == Str2Int(s1);
  assert n2 == Str2Int(s2);

  if n1 < n2 {
    res := -1;
  } else if n1 == n2 {
    res := 0;
  } else {
    res := 1;
  }
}
// </vc-code>

