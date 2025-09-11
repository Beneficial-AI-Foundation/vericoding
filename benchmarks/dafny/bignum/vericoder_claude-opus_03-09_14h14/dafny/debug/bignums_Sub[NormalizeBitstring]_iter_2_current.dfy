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

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
  calc {
    Str2Int("0");
    == 2 * Str2Int("") + 0;
    == 2 * 0 + 0;
    == 0;
  }
}

lemma Str2IntOne()
  ensures Str2Int("1") == 1
{
  calc {
    Str2Int("1");
    == 2 * Str2Int("") + 1;
    == 2 * 0 + 1;
    == 1;
  }
}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  var sc := s + [c];
  assert ValidBitString(sc);
  assert sc[0..|sc|-1] == s;
  assert sc[|sc|-1] == c;
}

lemma Str2IntPrepend(c: char, s: string)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString([c] + s)
  ensures Str2Int([c] + s) == (if c == '1' then Pow2(|s|) else 0) + Str2Int(s)
{
  var cs := [c] + s;
  assert ValidBitString(cs);
  if |s| == 0 {
    assert Str2Int([c]) == if c == '1' then 1 else 0;
  } else {
    assert cs[0..|cs|-1] == [c] + s[0..|s|-1];
    assert cs[|cs|-1] == s[|s|-1];
  }
}

function BorrowSub(a: char, b: char, borrow: nat): (nat, char)
  requires a == '0' || a == '1'
  requires b == '0' || b == '1'
  requires borrow == 0 || borrow == 1
{
  var av := if a == '1' then 1 else 0;
  var bv := if b == '1' then 1 else 0;
  var diff := av - bv - borrow;
  if diff >= 0 then
    (0, if diff == 1 then '1' else '0')
  else
    (1, '1')
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
  var result := "";
  var borrow := 0;
  var i1 := |s1| - 1;
  var i2 := |s2| - 1;
  
  ghost var pow := 1;
  ghost var accumulated := 0;
  
  while i1 >= 0 || i2 >= 0 || borrow > 0
    invariant -1 <= i1 < |s1|
    invariant -1 <= i2 < |s2|
    invariant borrow == 0 || borrow == 1
    invariant ValidBitString(result)
    invariant pow == if |result| == 0 then 1 else Pow2(|result|)
    invariant accumulated == Str2Int(result)
    invariant i1 >= 0 ==> i1 == |s1| - |result| - 1
    invariant i2 >= 0 ==> i2 == |s2| - |result| - 1
    invariant i1 < 0 ==> |result| >= |s1|
    invariant i2 < 0 ==> |result| >= |s2|
    invariant accumulated + borrow * pow + 
             (if i1 >= 0 then Str2Int(s1[0..i1+1]) * pow else 0) ==
             (if i2 >= 0 then Str2Int(s2[0..i2+1]) * pow else 0) + Str2Int(s1) - Str2Int(s2)
    decreases if i1 >= 0 then i1 else -1, if i2 >= 0 then i2 else -1
  {
    var d1 := if i1 >= 0 then s1[i1] else '0';
    var d2 := if i2 >= 0 then s2[i2] else '0';
    
    var (newBorrow, digit) := BorrowSub(d1, d2, borrow);
    result := [digit] + result;
    borrow := newBorrow;
    
    ghost var oldAccumulated := accumulated;
    accumulated := Str2Int(result);
    pow := pow * 2;
    
    if i1 >= 0 { i1 := i1 - 1; }
    if i2 >= 0 { i2 := i2 - 1; }
  }
  
  res := NormalizeBitString(result);
}
// </vc-code>

