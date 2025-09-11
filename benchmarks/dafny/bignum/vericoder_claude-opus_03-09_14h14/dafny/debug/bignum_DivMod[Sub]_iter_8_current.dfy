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

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntSingleZero()
  ensures Str2Int("0") == 0
{
}

lemma Str2IntSingleOne()
  ensures Str2Int("1") == 1
{
}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  if |s| == 0 {
    assert s + [c] == [c];
    calc {
      Str2Int([c]);
      == (2 * Str2Int([]) + (if c == '1' then 1 else 0));
      == (2 * 0 + (if c == '1' then 1 else 0));
      == (if c == '1' then 1 else 0);
    }
  } else {
    var s' := s + [c];
    assert s'[0..|s'|-1] == s;
    assert s'[|s'|-1] == c;
  }
}

lemma ValidBitStringConcat(s1: string, s2: string)
  requires ValidBitString(s1)
  requires ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
{
}

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

lemma Power2Monotonic(n: nat, m: nat)
  requires n <= m
  ensures Power2(n) <= Power2(m)
{
  if n == m {
  } else {
    Power2Monotonic(n, m-1);
  }
}

lemma Str2IntBounds(s: string)
  requires ValidBitString(s)
  ensures 0 <= Str2Int(s) < Power2(|s|)
  ensures |s| > 0 && s[0] == '1' ==> Str2Int(s) >= Power2(|s| - 1)
{
  if |s| == 0 {
  } else if |s| == 1 {
    if s[0] == '0' {
      Str2IntSingleZero();
    } else {
      Str2IntSingleOne();
    }
  } else {
    var prefix := s[0..|s|-1];
    Str2IntBounds(prefix);
    if s[0] == '1' {
      Str2IntBounds(prefix);
      assert Str2Int(prefix) >= Power2(|prefix| - 1);
    }
  }
}

lemma Str2IntLeadingZeros(s: string, i: nat)
  requires ValidBitString(s)
  requires i <= |s|
  requires forall k | 0 <= k < i :: s[k] == '0'
  ensures i == |s| ==> Str2Int(s) == 0
  ensures i < |s| ==> Str2Int(s) == Str2Int(s[i..])
  decreases |s| - i
{
  if i == |s| {
    if |s| == 0 {
      Str2IntEmpty();
    } else {
      assert s[|s|-1] == '0';
      if |s| == 1 {
        Str2IntSingleZero();
      } else {
        var prefix := s[0..|s|-1];
        assert ValidBitString(prefix);
        assert |prefix| == |s| - 1;
        assert i - 1 <= |prefix|;
        assert forall k | 0 <= k < i-1 :: prefix[k] == s[k] == '0';
        assert |prefix| - (i-1) == |s| - 1 - i + 1 == |s| - i < |s| - i + 1;
        Str2IntLeadingZeros(prefix, i-1);
      }
    }
  } else if i == 0 {
    assert s[i..] == s;
  } else {
    assert s[0] == '0';
    if |s| == 1 {
      Str2IntSingleZero();
      assert s[i..] == "";
      Str2IntEmpty();
    } else {
      var s' := s[1..];
      assert ValidBitString(s');
      assert |s'| == |s| - 1;
      assert i - 1 <= |s'|;
      assert forall k | 0 <= k < i-1 :: s'[k] == s[k+1] == '0';
      assert |s'| - (i-1) == |s| - 1 - i + 1 == |s| - i < |s| - i + 1;
      Str2IntLeadingZeros(s', i-1);
      assert s'[i-1..] == s[i..];
      
      calc {
        Str2Int(s);
        == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
        == { 
          assert s[0] == '0';
          var prefix := s[0..|s|-1];
          if |prefix| == 1 {
            assert prefix == "0";
            Str2IntSingleZero();
          } else {
            assert prefix[0] == '0';
            var prefixTail := prefix[1..];
            assert prefixTail == s[1..|s|-1] == s'[0..|s'|-1];
            calc {
              Str2Int(prefix);
              == 2 * Str2Int(prefix[0..|prefix|-1]) + (if prefix[|prefix|-1] == '1' then 1 else 0);
              == 2 * Str2Int(prefixTail) + (if s[|s|-2] == '1' then 1 else 0);
            }
          }
          assert Str2Int(prefix) == 2 * Str2Int(s'[0..|s'|-1]) + (if s[|s|-2] == '1' then 1 else 0);
          2 * (2 * Str2Int(s'[0..|s'|-1]) + (if s[|s|-2] == '1' then 1 else 0)) + (if s[|s|-1] == '1' then 1 else 0)
        }
        == 2 * Str2Int(s') + (if s[|s|-1] == '1' then 1 else 0);
        == Str2Int(s[i..]);
      }
    }
  }
}

lemma Str2IntComparison(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  requires |s1| > 0
  ensures (forall k | 0 <= k < |s1| :: s1[k] == s2[k]) ==> Str2Int(s1) == Str2Int(s2)
  ensures (exists j | 0 <= j < |s1| :: s1[j] != s2[j] && (forall k | 0 <= k < j :: s1[k] == s2[k])) ==>
          (forall j | 0 <= j < |s1| && s1[j] != s2[j] && (forall k | 0 <= k < j :: s1[k] == s2[k]) ::
           (s1[j] > s2[j] ==> Str2Int(s1) > Str2Int(s2)) &&
           (s1[j] < s2[j] ==> Str2Int(s1) < Str2Int(s2)))
{
  if |s1| == 1 {
    if s1[0] == s2[0] {
      assert Str2Int(s1) == Str2Int(s2);
    } else if s1[0] == '1' && s2[0] == '0' {
      Str2IntSingleOne();
      Str2IntSingleZero();
    } else {
      Str2IntSingleZero();
      Str2IntSingleOne();
    }
  } else {
    var prefix1 := s1[0..|s1|-1];
    var prefix2 := s2[0..|s2|-1];
    if forall k | 0 <= k < |s1| :: s1[k] == s2[k] {
      assert prefix1 == prefix2;
      assert s1[|s1|-1] == s2[|s2|-1];
    } else {
      forall j | 0 <= j < |s1| && s1[j] != s2[j] && (forall k | 0 <= k < j :: s1[k] == s2[k])
      ensures (s1[j] > s2[j] ==> Str2Int(s1) > Str2Int(s2)) &&
              (s1[j] < s2[j] ==> Str2Int(s1) < Str2Int(s2))
      {
        if j < |s1| - 1 {
          assert forall k | 0 <= k < j :: prefix1[k] == prefix2[k];
          assert prefix1[j] == s1[j];
          assert prefix2[j] == s2[j];
          Str2IntComparison(prefix1, prefix2);
        } else {
          assert j == |s1| - 1;
          assert prefix1 == prefix2;
        }
      }
    }
  }
}

method CompareStrings(s1: string, s2: string) returns (cmp: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures cmp == 0 ==> Str2Int(s1) == Str2Int(s2)
  ensures cmp > 0 ==> Str2Int(s1) > Str2Int(s2)
  ensures cmp < 0 ==> Str2Int(s1) < Str2Int(s2)
{
  // Remove leading zeros from s1
  var i1 := 0;
  while i1 < |s1| && s1[i1] == '0'
    invariant 0 <= i1 <= |s1|
    invariant forall k | 0 <= k < i1 :: s1[k] == '0'
  {
    i1 := i1 + 1;
  }
  var t1 := if i1 == |s1| then "0" else s1[i1..];
  assert ValidBitString(t1);
  Str2IntLeadingZeros(s1, i1);
  
  // Remove leading zeros from s2
  var i2 := 0;
  while i2 < |s2| && s2[i2] == '0'
    invariant 0 <= i2 <= |s2|
    invariant forall k | 0 <= k < i2 :: s2[k] == '0'
  {
    i2 := i2 + 1;
  }
  var t2 := if i2 == |s2| then "0" else s2[i2..];
  assert ValidBitString(t2);
  Str2IntLeadingZeros(s2, i2);
  
  // Compare lengths first
  if |t1| < |t2| {
    cmp := -1;
    // Prove that shorter binary string has smaller value when no leading zeros
    assert |t2| > 0 && t2[0] == '1';
    Str2IntBounds(t2);
    Str2IntBounds(t1);
    Power2Monotonic(|t1|, |t2| - 1);
  } else if |t1| > |t2| {
    cmp := 1;
    // Prove that longer binary string has larger value when no leading zeros
    assert |t1| > 0 && t1[0] == '1';
    Str2IntBounds(t1);
    Str2IntBounds(t2);
    Power2Monotonic(|t2|, |t1| - 1);
  } else {
    // Same length, compare lexicographically
    var j := 0;
    cmp := 0;
    while j < |t1| && cmp == 0
      invariant 0 <= j <= |t1|
      invariant |t1| == |t2|
      invariant cmp == 0 ==> forall k | 0 <= k < j :: t1[k] == t2[k]
      invariant cmp < 0 ==> exists jj | 0 <= jj < j :: t1[jj] < t2[jj] && (forall k | 0 <= k < jj :: t1[k] == t2[k])
      invariant cmp > 0 ==> exists jj | 0 <= jj < j :: t1[jj] > t2[jj] && (forall k | 0 <= k < jj :: t1[k] == t2[k])
    {
      if t1[j] < t2[j] {
        cmp := -1;
      } else if t1[j] > t2[j] {
        cmp := 1;
      }
      j := j + 1;
    }
    
    if |t1| > 0 {
      Str2IntComparison(t1, t2);
      if cmp != 0 {
        var witnessIdx :| 0 <= witnessIdx < |t1| && t1[witnessIdx] != t2[witnessIdx] && (forall k | 0 <= k < witnessIdx :: t1[k] == t2[k]);
      }
    } else {
      Str2IntEmpty();
    }
  }
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
  quotient := "";
  remainder := "";
  
  var i := 0;
  while i < |dividend|
    invariant 0 <= i <= |dividend|
    invariant ValidBitString(quotient)
    invariant ValidBitString(remainder)
    invariant i > 0 ==> Str2Int(dividend[..i]) == Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder)
    invariant i == 0 ==> quotient == "" && remainder == ""
    invariant Str2Int(remainder) < Str2Int(divisor)
  {
    var bit := dividend[i];
    Str2IntAppend(remainder, bit);
    remainder := remainder + [bit];
    
    var cmp := CompareStrings(remainder, divisor);
    if cmp >= 0 {
      var oldRemainder := remainder;
      remainder := Sub(remainder, divisor);
      Str2IntAppend(quotient, '1');
      quotient := quotient + ['1'];
      
      if i > 0 {
        assert dividend[..i+1] == dividend[..i] + [bit];
        Str2IntAppend(dividend[..i], bit);
      } else {
        assert dividend[..1] == [bit];
      }
    } else {
      Str2IntAppend(quotient, '0');
      quotient := quotient + ['0'];
      
      if i > 0 {
        assert dividend[..i+1] == dividend[..i] + [bit];
        Str2IntAppend(dividend[..i], bit);
      } else {
        assert dividend[..1] == [bit];
      }
    }
    
    i := i + 1;
  }
  
  assert dividend[..|dividend|] == dividend;
  
  if quotient == "" {
    quotient := "0";
    Str2IntSingleZero();
  }
  
  if remainder == "" {
    remainder := "0";
    Str2IntSingleZero();
  }
}
// </vc-code>

