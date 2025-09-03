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
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntSingle0()
  ensures Str2Int("0") == 0
{
}

lemma Str2IntSingle1()
  ensures Str2Int("1") == 1
{
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma Int2StrCorrect(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 {
    Str2IntSingle0();
  } else if n == 1 {
    Str2IntSingle1();
  } else {
    Int2StrCorrect(n / 2);
    var s := Int2Str(n / 2);
    var last := if n % 2 == 0 then "0" else "1";
    assert Int2Str(n) == s + last;
    Str2IntAppend(s, last);
  }
}

lemma Str2IntAppend(s: string, c: string)
  requires ValidBitString(s)
  requires ValidBitString(c)
  requires |c| == 1
  ensures Str2Int(s + c) == 2 * Str2Int(s) + (if c[0] == '1' then 1 else 0)
{
  if |s| == 0 {
    assert s + c == c;
    assert Str2Int(c) == if c[0] == '1' then 1 else 0;
  } else {
    calc {
      Str2Int(s + c);
      == { assert (s + c)[0..|s + c|-1] == s; }
      2 * Str2Int(s) + (if (s + c)[|s + c|-1] == '1' then 1 else 0);
      == { assert (s + c)[|s + c|-1] == c[0]; }
      2 * Str2Int(s) + (if c[0] == '1' then 1 else 0);
    }
  }
}

lemma Str2IntPrefix(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var prefix := s[0..i];
  var nextChar := s[i..i+1];
  assert s[0..i+1] == prefix + nextChar;
  assert |nextChar| == 1;
  assert nextChar[0] == s[i];
  Str2IntAppend(prefix, nextChar);
}

lemma DivModProperty(dividendVal: nat, divisorVal: nat, q: nat, r: nat)
  requires divisorVal > 0
  requires q * divisorVal + r == dividendVal
  requires 0 <= r < divisorVal
  ensures q == dividendVal / divisorVal
  ensures r == dividendVal % divisorVal
{
}

method ComputeDivMod(dividendVal: nat, divisorVal: nat) returns (q: nat, r: nat)
  requires divisorVal > 0
  ensures q == dividendVal / divisorVal
  ensures r == dividendVal % divisorVal
{
  q := 0;
  r := dividendVal;
  
  while r >= divisorVal
    invariant q * divisorVal + r == dividendVal
    invariant 0 <= r
    decreases r
  {
    q := q + 1;
    r := r - divisorVal;
  }
  
  assert r < divisorVal;
  assert q * divisorVal + r == dividendVal;
  DivModProperty(dividendVal, divisorVal, q, r);
}

method StringToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
  {
    var old_n := n;
    n := n * 2;
    if s[i] == '1' {
      n := n + 1;
    }
    
    assert s[0..i+1] == s[0..i+1];
    if i > 0 {
      Str2IntPrefix(s, i);
      assert n == 2 * old_n + (if s[i] == '1' then 1 else 0);
      assert old_n == Str2Int(s[0..i]);
      assert n == Str2Int(s[0..i+1]);
    } else {
      assert s[0..1] == [s[0]];
      assert n == (if s[0] == '1' then 1 else 0);
      assert Str2Int(s[0..1]) == (if s[0] == '1' then 1 else 0);
    }
    
    i := i + 1;
  }
  
  assert i == |s|;
  assert s[0..|s|] == s;
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
  var dividendVal := StringToNat(dividend);
  var divisorVal := StringToNat(divisor);
  
  assert dividendVal == Str2Int(dividend);
  assert divisorVal == Str2Int(divisor);
  
  var q, r := ComputeDivMod(dividendVal, divisorVal);
  
  assert q == dividendVal / divisorVal;
  assert r == dividendVal % divisorVal;
  assert q == Str2Int(dividend) / Str2Int(divisor);
  assert r == Str2Int(dividend) % Str2Int(divisor);
  
  quotient := Int2Str(q);
  remainder := Int2Str(r);
  
  Int2StrCorrect(q);
  Int2StrCorrect(r);
  
  assert Str2Int(quotient) == q;
  assert Str2Int(remainder) == r;
}
// </vc-code>

