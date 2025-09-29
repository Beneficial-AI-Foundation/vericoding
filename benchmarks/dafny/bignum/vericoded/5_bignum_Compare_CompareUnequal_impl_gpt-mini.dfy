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
  // Unfold definition explicitly.
  assert Str2Int(s) ==
    (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  assert |s| > 0;
  assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
}

lemma Str2Int_Full(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s[0..|s|]) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // both are 0 by definition
    assert Str2Int(s) == 0;
    assert Str2Int(s[0..|s|]) == 0;
  } else {
    // Use Snoc on s and on its full substring (which is equal to s).
    Str2Int_Snoc(s);
    Str2Int_Snoc(s[0..|s|]);
    // Relate the inner substrings and last characters.
    assert (s[0..|s|])[0..|s|-1] == s[0..|s|-1];
    assert (s[0..|s|])[|s|-1] == s[|s|-1];
    // Apply induction on the prefix.
    Str2Int_Full(s[0..|s|-1]);
    // Now both sides expand to the same expression.
    assert Str2Int(s[0..|s|]) == 2 * Str2Int((s[0..|s|])[0..|s|-1]) + (if (s[0..|s|])[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s)         == 2 * Str2Int(s[0..|s|-1])            + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int((s[0..|s|])[0..|s|-1]) == Str2Int(s[0..|s|-1]);
    assert (if (s[0..|s|])[|s|-1] == '1' then 1 else 0) == (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s[0..|s|]) == Str2Int(s);
  }
}

lemma SubstringIndex(s: string, i: int)
  requires 0 < i <= |s|
  ensures (s[0..i])[0..i-1] == s[0..i-1]
  ensures (s[0..i])[i-1] == s[i-1]
{
  // For 0 <= j < i we have (s[0..i])[j] == s[j], hence the prefix equality and last character equality.
  assert forall j | 0 <= j < i :: (s[0..i])[j] == s[j];
  assert (s[0..i])[0..i-1] == s[0..i-1];
  assert (s[0..i])[i-1] == s[i-1];
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
    var old_i := i;
    var old_n := n1;
    ValidSubstring(s1, old_i + 1);
    var bit := if s1[old_i] == '1' then 1 else 0;
    var new_n := 2 * old_n + bit;
    i := old_i + 1;
    n1 := new_n;
    // Apply Snoc to the newly extended substring s1[0..i].
    Str2Int_Snoc(s1[0..i]);
    SubstringIndex(s1, i);
    // Relate old_n to the previous substring and bit to the last character.
    assert old_n == Str2Int(s1[0..i-1]);
    assert Str2Int(s1[0..i]) == 2 * Str2Int(s1[0..i-1]) + (if s1[i-1] == '1' then 1 else 0);
    assert bit == (if s1[i-1] == '1' then 1 else 0);
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
    var old_i := i;
    var old_n := n2;
    ValidSubstring(s2, old_i + 1);
    var bit := if s2[old_i] == '1' then 1 else 0;
    var new_n := 2 * old_n + bit;
    i := old_i + 1;
    n2 := new_n;
    Str2Int_Snoc(s2[0..i]);
    SubstringIndex(s2, i);
    assert old_n == Str2Int(s2[0..i-1]);
    assert Str2Int(s2[0..i]) == 2 * Str2Int(s2[0..i-1]) + (if s2[i-1] == '1' then 1 else 0);
    assert bit == (if s2[i-1] == '1' then 1 else 0);
    assert n2 == Str2Int(s2[0..i]);
  }

  // Convert full-substring representations to Str2Int of the full strings.
  assert n1 == Str2Int(s1[0..|s1|]);
  assert n2 == Str2Int(s2[0..|s2|]);
  Str2Int_Full(s1);
  Str2Int_Full(s2);
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

