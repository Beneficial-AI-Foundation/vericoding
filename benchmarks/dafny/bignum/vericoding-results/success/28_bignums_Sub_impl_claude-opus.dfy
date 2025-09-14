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
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{}

lemma Str2IntSingle(c: char)
  requires c == '0' || c == '1'
  ensures Str2Int([c]) == if c == '1' then 1 else 0
{}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  if |s| == 0 {
    assert s + [c] == [c];
    Str2IntSingle(c);
  } else {
    calc == {
      Str2Int(s + [c]);
      2 * Str2Int((s + [c])[0..|s + [c]|-1]) + (if (s + [c])[|s + [c]|-1] == '1' then 1 else 0);
      {assert (s + [c])[0..|s + [c]|-1] == s;}
      {assert (s + [c])[|s + [c]|-1] == c;}
      2 * Str2Int(s) + (if c == '1' then 1 else 0);
    }
  }
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then "" else Int2Str(n / 2) + [if n % 2 == 1 then '1' else '0']
}

lemma Int2StrCorrectness(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 {
    Str2IntEmpty();
  } else {
    var s := Int2Str(n / 2);
    var c := if n % 2 == 1 then '1' else '0';
    Int2StrCorrectness(n / 2);
    assert ValidBitString(s);
    assert c == '0' || c == '1';
    Str2IntAppend(s, c);
    calc == {
      Str2Int(Int2Str(n));
      Str2Int(s + [c]);
      2 * Str2Int(s) + (if c == '1' then 1 else 0);
      2 * (n / 2) + (if n % 2 == 1 then 1 else 0);
      n;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var n1 := 0;
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant n1 == Str2Int(s1[0..i])
  {
    assert s1[0..i+1] == s1[0..i] + [s1[i]];
    Str2IntAppend(s1[0..i], s1[i]);
    n1 := 2 * n1 + (if s1[i] == '1' then 1 else 0);
    i := i + 1;
  }
  assert s1[0..|s1|] == s1;
  
  var n2 := 0;
  i := 0;
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant n2 == Str2Int(s2[0..i])
  {
    assert s2[0..i+1] == s2[0..i] + [s2[i]];
    Str2IntAppend(s2[0..i], s2[i]);
    n2 := 2 * n2 + (if s2[i] == '1' then 1 else 0);
    i := i + 1;
  }
  assert s2[0..|s2|] == s2;
  
  var diff := n1 - n2;
  res := Int2Str(diff);
  Int2StrCorrectness(diff);
}
// </vc-code>

