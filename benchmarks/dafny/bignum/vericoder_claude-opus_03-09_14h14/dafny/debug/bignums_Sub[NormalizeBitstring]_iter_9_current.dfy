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
    assert Pow2(0) == 1;
  } else {
    assert cs[0..|cs|-1] == [c] + s[0..|s|-1];
    assert cs[|cs|-1] == s[|s|-1];
    Str2IntPrepend(c, s[0..|s|-1]);
    calc {
      Str2Int([c] + s);
      == 2 * Str2Int([c] + s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == 2 * ((if c == '1' then Pow2(|s|-1) else 0) + Str2Int(s[0..|s|-1])) + (if s[|s|-1] == '1' then 1 else 0);
      == (if c == '1' then 2 * Pow2(|s|-1) else 0) + 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == (if c == '1' then Pow2(|s|) else 0) + Str2Int(s);
    }
  }
}

function BorrowSub(a: char, b: char, borrow: nat): (nat, char)
  requires a == '0' || a == '1'
  requires b == '0' || b == '1'
  requires borrow == 0 || borrow == 1
  ensures var (newBorrow, digit) := BorrowSub(a, b, borrow);
          var av := if a == '1' then 1 else 0;
          var bv := if b == '1' then 1 else 0;
          var dv := if digit == '1' then 1 else 0;
          av - bv - borrow == dv - 2 * newBorrow
{
  var av := if a == '1' then 1 else 0;
  var bv := if b == '1' then 1 else 0;
  var diff := av - bv - borrow;
  if diff >= 0 then
    var digit := if diff == 1 then '1' else '0';
    assert diff == 0 || diff == 1;
    assert diff == 1 ==> digit == '1';
    assert diff == 0 ==> digit == '0';
    var dv := if digit == '1' then 1 else 0;
    assert diff == dv;
    assert av - bv - borrow == dv - 2 * 0;
    (0, digit)
  else
    assert diff == -1 || diff == -2;
    assert diff == -1 ==> av - bv - borrow == 1 - 2 * 1;
    assert diff == -2 ==> av - bv - borrow == 0 - 2 * 1;
    var digit := if diff == -1 then '1' else '0';
    var dv := if digit == '1' then 1 else 0;
    assert av - bv - borrow == dv - 2 * 1;
    (1, digit)
}

lemma BorrowSubCorrectness(a: char, b: char, borrow: nat)
  requires a == '0' || a == '1'
  requires b == '0' || b == '1'
  requires borrow == 0 || borrow == 1
  ensures var (newBorrow, digit) := BorrowSub(a, b, borrow);
          var av := if a == '1' then 1 else 0;
          var bv := if b == '1' then 1 else 0;
          var dv := if digit == '1' then 1 else 0;
          av - bv - borrow == dv - 2 * newBorrow
{
}

lemma Str2IntSuffix(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  ensures Str2Int(s) == Str2Int(s[0..i]) * Pow2(|s| - i) + Str2Int(s[i..])
  decreases |s| - i
{
  if i == |s| {
    assert s[0..i] == s;
    assert s[i..] == "";
    Str2IntEmpty();
    assert Pow2(0) == 1;
  } else if i == 0 {
    assert s[0..i] == "";
    assert s[i..] == s;
    Str2IntEmpty();
  } else if |s| == 0 {
    // Base case: empty string
  } else {
    // Use recursion on the tail of the string
    assert s == s[0..|s|-1] + [s[|s|-1]];
    var last := s[|s|-1];
    var prefix := s[0..|s|-1];
    
    if i == |s| - 1 {
      assert s[0..i] == prefix;
      assert s[i..] == [last];
      calc {
        Str2Int(s);
        == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
        == Str2Int(s[0..i]) * 2 + Str2Int(s[i..]);
        == Str2Int(s[0..i]) * Pow2(1) + Str2Int(s[i..]);
      }
    } else if i < |s| - 1 {
      Str2IntSuffix(prefix, i);
      assert prefix[0..i] == s[0..i];
      assert prefix[i..] == s[i..|s|-1];
      
      calc {
        Str2Int(s);
        == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
        == 2 * (Str2Int(s[0..i]) * Pow2(|prefix| - i) + Str2Int(s[i..|s|-1])) + (if last == '1' then 1 else 0);
        == Str2Int(s[0..i]) * Pow2(|s| - i) + (2 * Str2Int(s[i..|s|-1]) + (if last == '1' then 1 else 0));
        == { Str2IntAppend(s[i..|s|-1], last); assert s[i..] == s[i..|s|-1] + [last]; }
           Str2Int(s[0..i]) * Pow2(|s| - i) + Str2Int(s[i..]);
      }
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
    invariant pow == Pow2(|result|)
    invariant accumulated == Str2Int(result)
    invariant i1 >= 0 && i2 >= 0 ==> 
              accumulated + borrow * pow + Str2Int(s2[i2+1..]) == Str2Int(s1[i1+1..])
    invariant i1 >= 0 && i2 < 0 ==> 
              accumulated + borrow * pow == Str2Int(s1[i1+1..])
    invariant i1 < 0 && i2 >= 0 ==> 
              accumulated + borrow * pow + Str2Int(s2[i2+1..]) == 0
    invariant i1 < 0 && i2 < 0 ==> 
              accumulated == 0 && borrow == 0
    decreases i1 + i2 + 2, borrow
  {
    var d1 := if i1 >= 0 then s1[i1] else '0';
    var d2 := if i2 >= 0 then s2[i2] else '0';
    
    var (newBorrow, digit) := BorrowSub(d1, d2, borrow);
    
    // Ghost calculations for invariant maintenance
    ghost var oldResult := result;
    ghost var oldAccumulated := accumulated;
    
    result := [digit] + result;
    
    // Update ghost variables
    assert result == [digit] + oldResult;
    assert |result| == |oldResult| + 1;
    Str2IntPrepend(digit, oldResult);
    assert Str2Int(result) == (if digit == '1' then Pow2(|oldResult|) else 0) + Str2Int(oldResult);
    assert Str2Int(result) == (if digit == '1' then pow else 0) + oldAccumulated;
    
    // Apply BorrowSub correctness
    BorrowSubCorrectness(d1, d2, borrow);
    ghost var d1v := if d1 == '1' then 1 else 0;
    ghost var d2v := if d2 == '1' then 1 else 0;
    ghost var dv := if digit == '1' then 1 else 0;
    assert d1v - d2v - borrow == dv - 2 * newBorrow;
    
    // Update accumulated
    accumulated := Str2Int(result);
    pow := pow * 2;
    
    // Maintain invariant through suffix reasoning
    if i1 >= 0 && i2 >= 0 {
      assert s1[i1+1..] == s1[(i1+1)..|s1|];
      assert s2[i2+1..] == s2[(i2+1)..|s2|];
      
      if i1 > 0 {
        Str2IntSuffix(s1, i1);
        assert Str2Int(s1) == Str2Int(s1[0..i1]) * Pow2(|s1| - i1) + Str2Int(s1[i1..]);
        assert s1[i1..] == [s1[i1]] + s1[i1+1..];
        Str2IntPrepend(s1[i1], s1[i1+1..]);
        assert Str2Int(s1[i1..]) == d1v * Pow2(|s1[i1+1..]|) + Str2Int(s1[i1+1..]);
      }
      
      if i2 > 0 {
        Str2IntSuffix(s2, i2);
        assert Str2Int(s2) == Str2Int(s2[0..i2]) * Pow2(|s2| - i2) + Str2Int(s2[i2..]);
        assert s2[i2..] == [s2[i2]] + s2[i2+1..];
        Str2IntPrepend(s2[i2], s2[i2+1..]);
        assert Str2Int(s2[i2..]) == d2v * Pow2(|s2[i2+1..]|) + Str2Int(s2[i2+1..]);
      }
    }
    
    borrow := newBorrow;
    
    if i1 >= 0 {
      i1 := i1 - 1;
    }
    
    if i2 >= 0 {
      i2 := i2 - 1;
    }
  }
  
  res := NormalizeBitString(result);
}
// </vc-code>

