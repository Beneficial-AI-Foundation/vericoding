
method Main() {
  print "Examples:\n";

  var a := "1011";  // decimal 11

  var b := "1101";  // decimal 13

  print "a = ", a, " (decimal=", Str2Int(a), ")\n";
  print "b = ", b, " (decimal=", Str2Int(b), ")\n";

  var s := Add(a, b);
  print "a + b = ", s, " (decimal=", Str2Int(s), ")\n";

  // sub needs to know that the result will be positive
  Eleven();
  Thirteen();
  var d := Sub(b, a);
  print "b - a = ", d, " (decimal=", Str2Int(d), ")\n";

  var m := Mul(a, b);
  print "a * b = ", m, " (decimal=", Str2Int(m), ")\n";

  var z := "0";
  var sumZ := Add(a, z);
  print a, " + 0 = ", sumZ, " (decimal=", Str2Int(sumZ), ")\n";

  // Convert integer -> string, then back
  var n := 9999;
  var sN := Int2Str(n);
  print "9999 -> ", sN, " -> ", Str2Int(sN), "\n";
}


// Eleven and Thirteen will be used in Main

lemma Eleven()
  ensures Str2Int("1011") == 11
{
  var s := "1011";
  calc {
    Str2Int(s);
  ==
    2*Str2Int(s[..3]) + 1;
  ==
    {assert s[..3] == "101";}
    2*Str2Int("101") + 1;
  ==
    {
      assert 2*Str2Int("10")+1 == Str2Int("101");}
    2*(2*Str2Int("10")+1) + 1;
  ==
    4*Str2Int("10") + 3;
  ==
    11;}
}

lemma Thirteen()
  ensures Str2Int("1101") == 13
{
  var s := "1101";
  calc {
    Str2Int(s);
  ==
    2*Str2Int(s[..3]) + 1;
  ==
    {assert s[..3] == "110";}
    2*Str2Int("110") + 1;
  ==
    {
      assert 2*Str2Int("11")+0 == Str2Int("110");}
    2*(2*Str2Int("11")+0) + 1;
  ==
    4*Str2Int("11") + 1;
  ==
    {assert Str2Int("11") == 3;}
    4*3 + 1;
  ==
    13;
  }
}


// ----------------------------------------------------
// Int2Str: nat -> bit-string (reference function)
//    - "0" if n=0
//    - no leading zeros otherwise
// ----------------------------------------------------
function Int2Str(n: nat): string
  // I added the following post-condition because Str2Int requires it
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then
    "0"

  else (if n == 1
        then "1"
        else (
            // Recursively build from most significant bits.
            // The last character added is (n % 2).
            assert ValidBitString(Int2Str(n/2));
            assert Str2Int(Int2Str(n/2)) == n/2;
            Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
          )
       )
}

// simulates the exponentiation we do on bistrings through bit decomposition and repeated squaring
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  reveal Exp_int();

  Exp_int_greater_than_0(2,n);

  var first_bit := y / Exp_int(2,n);
  var remainder := y % Exp_int(2,n);
  var first_term := first_bit * Exp_int(2,n);
  assert y == first_term + remainder;

  if n == 0 {
    assert y == 0 || y == 1;
    if y == 0 {
      assert Exp_int(x,y) == 1;
      assert 1 % z == 1;
      res := 1;
      return;
    }
    else if y == 1 {
      assert Exp_int(x,y) == x;
      res := x % z;
      return;
    }
  } else if first_term == 0 {
    assert n > 0;
    res := ModExp_int(x,remainder, n-1,z);
    return;
  }
  else {
    ModExpDistributivity_int(x,first_term,remainder,z);
    assert Exp_int(x,y) % z == ((Exp_int(x,first_term) % z) * (Exp_int(x,remainder) % z)) % z;
    var exp_first := ModExpPow2_int(x,first_term, n, z);
    var exp_remainder := ModExp_int(x,remainder,n-1,z);
    res :=  (exp_first * exp_remainder) % z;
    return;
  }

}

lemma Exp_int_greater_than_0(x: nat, y: nat)
  requires x > 0
  ensures Exp_int(x, y) > 0
{
  reveal Exp_int();
  if y == 0 {
    return;
  } else {
    Exp_int_greater_than_0(x, y - 1);
    return;
  }
}


// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  reveal Exp_int();
  if n == 0 {
    res := Exp_int(x,1) % z;
    return;
  }
  else {
    assert n > 0;
    var y' := Exp_int(2,n-1);
    var res' := ModExpPow2_int(x,y', n-1, z);
    res := (res' * res') % z; // squaring
    ModExpDistributivity_int(x,y',y',z);
    return;
  }
}

// computes (s1^s2) % s3 for bitstrings s1,s2,s3
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
{
  var n := |sy|;
  var zero_tail := Zeros(n-1);
  var first_term := sy[..1]+zero_tail;
  var second_term := sy[1..];

  Str2IntLemma(sy,0);
  Str2IntLemma(first_term,0);


  if |sy| == 1 {
    assert Str2Int(sy) == Str2Int(first_term);
    res := ModExpPow2(sx,sy,n-1,sz);
    return;
  }
  else {
    // CODE
    var sy_sum := Add(first_term,second_term);
    var first_res := ModExpPow2(sx,first_term,n-1,sz);
    var second_res := ModExp(sx,second_term,sz);
    var plain_res := Mul(first_res,second_res);
    // NOTE: do we need modular multiplication to keep strings as short as possible ?
    var remainder,quotient := DivMod(plain_res,sz);
    res := quotient;
    // PROOF
    assert Str2Int(res) == ( Str2Int(first_res) * Str2Int(second_res) ) % Str2Int(sz);
    ghost var x := Str2Int(sx);
    ghost var y1,y2 := Str2Int(first_term), Str2Int(second_term);
    ghost var z := Str2Int(sz);

    assert Str2Int(sy_sum) == Str2Int(sy) == y1 + y2; //Str2Int(first_term) + Str2Int(second_term);
    assert Str2Int(first_res) == Exp_int(x,y1) % z;
    assert Str2Int(second_res) == Exp_int(x,y2) % z;
    assert Exp_int(x,Str2Int(sy)) % z ==  Exp_int(x,y1+y2) % z;
    ModExpDistributivity_int(x,y1, y2,z);
    assert Exp_int(x,y1+y2) % z == (Exp_int(x,y1) % z) * (Exp_int(x,y2) % z) % z;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  }

}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  if n == 0 {
    assert Str2Int("")==0; s :="";
  }
  else {
    var st := Zeros(n - 1);
    assert ValidBitString(st);
    assert Str2Int(st) == 0;
    assert |st| == n - 1;
    s := "0" + st;
    assert ValidBitString(s);
    assert s[0] == '0';
    assert s[1..|s|] == st;
    Str2IntLemma(s, 0);
    assert Str2Int(s) == Str2Int("0") * Exp_int(2, |s| - 1) + Str2Int(st);
    assert Str2Int(s) == 0 * Exp_int(2, |s| - 1) + Str2Int(st);
    assert Str2Int(s) == Str2Int(st);
    assert Str2Int(s) == 0;
    assert AllZero(s);
  }
}

predicate AllZero(s: string)
{
  |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}

// computes (sx^sy) % sz for bitstrings sx,sy,sz when str2int(sy) == 2^n
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  reveal Exp_int();
  if Str2Int(sy) == 0 {
    res := "1";
    return;
  }
  else if n == 0 {
    var quotient,remainder := DivMod(sx, sz);
    res := remainder;
    return;
  }
  else {
    // CODE
    var sy' := sy[..|sy|-1];
    var sy_sum := Add(sy',sy');
    var res' := ModExpPow2(sx,sy', n-1, sz);
    res := Mul(res',res'); // squaring
    // PROOF
    assert n > 0; assert |sy| > 1;
    assert Str2Int(sy) == Exp_int(2,n);
    Str2IntLemma(sy,|sy|-2);
    assert Str2Int(sy[|sy|-1..|sy|]) == 0;
    assert Str2Int(sy) == Str2Int(sy') * Exp_int(2,1) + Str2Int(sy[|sy|-1..|sy|]);
    assert Str2Int(sy') == Exp_int(2,n-1);
    assert Str2Int(sy) == Str2Int(sy_sum);
    assert Str2Int(res') ==  Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz);
    assert Str2Int(res) == (Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz));

    // CODE
    var quotient, remainder := DivMod(res, sz);
    res := remainder;
    // PROOF
    assert Str2Int(res) == ((Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz))) % Str2Int(sz);
    ModExpDistributivity_int(Str2Int(sx),Str2Int(sy'),Str2Int(sy'),Str2Int(sz));
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  }

}

lemma Str2IntLemma(s: string, i: nat)
  requires ValidBitString(s)
  // requires n == |s| - 1
  requires 0 <= i <= |s|-1
  ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{
  Str2IntLemmaAux(s, i);
  reveal OStr2Int;
}

lemma Str2IntLemmaAux(s: string, i: nat)
  requires ValidBitString(s)
  // requires n == |s| - 1
  requires 0 <= i <= |s|-1
  ensures OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..])
{
  assert s == s[..|s|];
  if |s| == 0 || s == "0" {
    assert OStr2Int(s) == 0 by {reveal OStr2Int; assert Str2Int(s) == 0;}
    assert ValidBitString(s[..i+1]) && ValidBitString(s[i+1..]);
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..]) by {reveal OStr2Int;}
  } else if s == "1" {
    assert OStr2Int(s) == 1 by {reveal OStr2Int; assert Str2Int(s) == 1;}
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..]) by {reveal OStr2Int; reveal Exp_int;}
  } else if i == |s|-1 {
    // s[..i+1] == s and s[i+1..|s|] == ""
    assert OStr2Int(s) == OStr2Int(s[..|s|]);
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..]) by {reveal OStr2Int; reveal Exp_int;}
  } else {
    assert i < |s|-1;

    // Inductive step: apply lemma to the prefix s[..|s|-1]
    var prefix: string := s[..|s|-1];
    assert ValidBitString(prefix);
    Str2IntLemmaAux(prefix, i);

    // The induction hypothesis ensures:
    // OStr2Int(prefix) == OStr2Int(s[..i+1]) * Exp_int(2, (|s|-1-1) - i) + OStr2Int(s[i+1..|s|-1])
    assert prefix == prefix[..|s|-1];
    assert ValidBitString(prefix[i+1..|s|-1]);
    assert OStr2Int(prefix[..|s|-1]) == OStr2Int(prefix[..i+1]) * Exp_int(2, (|s|-1-1) - i) + OStr2Int(prefix[i+1..|s|-1]); // justified by lemma postcondition

    // By definition: OStr2Int(s) = 2 * OStr2Int(prefix) + char2int(s[|s|-1])
    assert prefix + s[|s|-1..|s|] == s[..|s|];
    assert OStr2Int(s) == 2 * OStr2Int(prefix) + char2int(s[|s|-1]) by {reveal OStr2Int;}
    assert OStr2Int(s) == 2 * (OStr2Int(prefix[..i+1]) * Exp_int(2, (|s|-1-1) - i) + OStr2Int(prefix[i+1..|s|-1])) + char2int(s[|s|-1]);
    assert s[..i+1] == prefix[..i+1] && s[i+1..|s|-1] == prefix[i+1..|s|-1];
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + 2 * OStr2Int(s[i+1..|s|-1]) + char2int(s[|s|-1]) by {reveal Exp_int;}

    // By definition: OStr2Int(s[i+1..|s|]) = 2 * OStr2Int(s[i+1..|s|-1]) + char2int(s[|s|-1])
    assert |s[i+1..|s|]| > 0;
    assert s[i+1..|s|] == s[i+1..|s|-1] + s[|s|-1..|s|];
    assert OStr2Int(s[i+1..|s|]) == 2 * OStr2Int(s[i+1..|s|-1]) + char2int(s[|s|-1]) by {reveal OStr2Int;}
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..|s|]);
  }
}

function char2int(c: char): nat
  requires c == '0' || c == '1'
{
  if c == '0' then 0 else 1
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  // Initialize working variables
  var q := "";
  var r := "";

  assert OStr2Int(r) < OStr2Int(divisor) by {reveal OStr2Int;}
  assert OStr2Int(dividend[..0]) == OStr2Int(r) + OStr2Int(q) * OStr2Int(divisor) by {reveal OStr2Int;}
  // See section 4.3.1 of The Art of Computer Programming, Volume 2.
  // i.e. PDF page 284 of
  // https://github.com/manjunath5496/The-Art-of-Computer-Programming-Books/blob/master/aoc(6).pdf
  // Except because the base is 2, we can find the next quotient digit by comparing r to the divisor,
  // instead of guessing and checking
  for i := 0 to |dividend|
    invariant ValidBitString(r)
    invariant ValidBitString(q)
    invariant OStr2Int(dividend[..i]) == OStr2Int(r) + OStr2Int(q) * OStr2Int(divisor)
    invariant OStr2Int(r) < OStr2Int(divisor)
  {
    // Shift remainder left and bring down next bit
    ghost var old_r := r;
    ghost var old_q := q;
    r := r + [dividend[i]];
    assert ValidBitString(r);
    ghost var d := if dividend[i] == '1' then 1 else 0;
    assert a1 : OStr2Int(r) == 2 * OStr2Int(old_r) + d by {reveal OStr2Int;}

    calc {
      OStr2Int(dividend[..i + 1]);
    ==
      {assert dividend[..i + 1][..|dividend[..i + 1]| -1 ] == dividend[..i];
       reveal OStr2Int;}
      2 * OStr2Int(dividend[..i]) + d;
    ==
      2 * (OStr2Int(old_r) + OStr2Int(old_q) * OStr2Int(divisor)) + d;
    ==
      {Rearrange2(OStr2Int(old_r), OStr2Int(old_q), OStr2Int(divisor),d);}
      2 * OStr2Int(old_q) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d);
    }

    // Check if divisor can be subtracted from current remainder
    var comparison := Compare(r, divisor);
    if comparison >= 0 {
      // Subtract divisor from remainder
      r := Sub(r, divisor);
      assert OStr2Int(r) < OStr2Int(divisor) by {reveal OStr2Int;}
      assert ValidBitString(r);
      assert a2: OStr2Int(r) == 2 * OStr2Int(old_r) + d - OStr2Int(divisor) by {reveal a1; reveal OStr2Int;}
      q := q + "1";
      assert ValidBitString(q);
      assert a3 : OStr2Int(q) == 2 * OStr2Int(old_q) + 1 by {reveal OStr2Int;}
      calc {
        2 * OStr2Int(old_q) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d);
      ==
        (2 * OStr2Int(old_q) + 1) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d - OStr2Int(divisor));
      ==
        {
          reveal a2;
          reveal a3;
        }
        OStr2Int(q) * OStr2Int(divisor) + OStr2Int(r);
      }
    } else {
      assert ValidBitString(r);
      assert OStr2Int(r) < OStr2Int(divisor) by {reveal OStr2Int;}
      q := q + "0";
      assert ValidBitString(q);
      assert OStr2Int(q) == 2 * OStr2Int(old_q) by {reveal OStr2Int;}
      calc {
        2 * OStr2Int(old_q) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d);
      ==
        {reveal OStr2Int;}
        OStr2Int(q) * OStr2Int(divisor) + OStr2Int(r);
      }
    }

  }
  calc {
    OStr2Int(dividend);
  ==
    {assert dividend[..|dividend|] == dividend;}
    OStr2Int(dividend[..|dividend|]);
  ==
    OStr2Int(r) + OStr2Int(q) * OStr2Int(divisor);
  }
  assert OStr2Int(r) < OStr2Int(divisor);

  quotient := q;
  remainder := r;
  QuotientIsEquivalent(OStr2Int(dividend), OStr2Int(divisor), OStr2Int(quotient), OStr2Int(remainder));
  assert Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor) by {reveal OStr2Int;}
  assert Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor) by {reveal OStr2Int;}
}

lemma Rearrange2(x:nat, y:nat, z:nat, w:nat)
  ensures 2 * (x + y * z) + w == 2 * y * z + (2 * x + w)
{
}

lemma QuotientIsEquivalent(dividend : nat, divisor: nat, quotient: nat, remainder: nat)
  requires dividend == divisor * quotient + remainder
  requires remainder < divisor
  requires divisor != 0
  ensures  dividend / divisor == quotient
  ensures  dividend % divisor == remainder
{
  assert (dividend / divisor) * divisor + dividend % divisor == dividend;
  assert (quotient - (dividend / divisor)) * divisor == dividend % divisor - remainder;
  Bounding(dividend % divisor - remainder, divisor, quotient - (dividend / divisor));
}




method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  // First normalize both strings
  var a := NormalizeBitString(s1);
  var b := NormalizeBitString(s2);

  // Compare lengths first
  if |a| < |b| {
    var res':= CompareUnequal(b, a);
    res := -res';
    return;
  }
  if |a| > |b| {
    res:= CompareUnequal(a, b);
    return;
  }

  // Equal lengths - compare bits from most significant
  if |a| == 0 {
    return 0;
  }

  // Recursive case - compare first bits then recurse on tails
  if a[0] < b[0] {
    return -1;
  }
  if a[0] > b[0] {
    return 1;
  }
  if a == "0" {
    return 0;
  }

  // First bits equal, compare rest
  assert a[0] == b[0];
  assert a[0] == '1';
  assert b[0] == '1';

  calc {
    Pow2(|b[1..]|) + Str2Int(b[1..]);
  ==
    {PrependDigitToString(1, b[1..]);}
    Str2Int(['1'] + b[1..]);
  ==
    {assert ['1'] + b[1..] == b;}
    Str2Int(b);
  }
  calc {
    Pow2(|a[1..]|) + Str2Int(a[1..]);
  ==
    {PrependDigitToString(1, a[1..]);}
    Str2Int(['1'] + a[1..]);
  ==
    {assert ['1'] + a[1..] == a;}
    Str2Int(a);
  }
  assert Str2Int(a) > Str2Int(a[1..]) by {
    Pow2Positive(|a[1..]|);
  }
  assert Str2Int(b) > Str2Int(b[1..]) by {
    Pow2Positive(|b[1..]|);
  }
  res := Compare(a[1..], b[1..]);
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
  var a := s1;
  var b := s2;

  // Split a into head and tail
  var head := a[0];
  var tail := a[1..];

  // Since a is normalized and longer than b, its first bit must be 1
  assert head == '1';
  calc {
    Pow2(|tail|) + Str2Int(tail);
  ==
    {PrependDigitToString(1, tail);}
    Str2Int(['1'] + tail);
  ==
    {assert ['1'] + tail == a;}
    Str2Int(a);
  }

  // The tail's value is bounded
  assert Str2Int(tail) < Pow2(|tail|) by {
    Bound(tail);
  }

  // b's value is bounded
  assert Str2Int(b) < Pow2(|b|) by {
    Bound(b);
  }

  // Since |b| < |a|, b's bound is smaller
  assert Pow2(|b|) <= Pow2(|a|-1) by {assert |b| <= |a|-1;
                                      Pow2Monotonic(|b|, |a|-1);}

  // Therefore a > b
  calc {
    Str2Int(a);
  ==
    Pow2(|a|-1) + Str2Int(tail);
  >=
    Pow2(|a|-1);
  >=
    Pow2(|b|);
  >
    Str2Int(b);
  }

  return 1;
}

lemma Pow2Monotonic(a: nat, b:nat)
  requires a <= b
  ensures Pow2(a) <= Pow2(b)
{
  if b-a == 0 {
    return;
  }
  if b-a == 1 {
    reveal Pow2;
    return;
  }
  reveal Pow2;
  Pow2Monotonic(a, b-1);
}

lemma ModExpDistributivity_int(x:nat, y1:int, y2:int, z:int)
  requires y1 >= 0 && y2 >= 0 && z > 0
  // NOTE: only positive exponents for now
  ensures Exp_int(x,y1+y2) % z == (Exp_int(x,y1) % z) * (Exp_int(x,y2) % z) % z
{
  ExpDistributivity_int(x,y1,y2);
  assert Exp_int(x,y1+y2) == Exp_int(x,y1) * Exp_int(x,y2);
  assert Exp_int(x,y1+y2) % z == (Exp_int(x,y1) * Exp_int(x,y2)) % z;
  ModuloDistributivityMul_int(Exp_int(x,y1),Exp_int(x,y2), z);
  assert (Exp_int(x,y1) * Exp_int(x,y2)) % z ==  (Exp_int(x,y1) % z) * (Exp_int(x,y2) % z) % z;
}


lemma ExpDistributivity_int(x:nat, y1:int, y2:int)
  requires y1 >= 0 && y2 >= 0
  // NOTE: only positive exponents for now
  ensures Exp_int(x,y1+y2) == Exp_int(x,y1) * Exp_int(x,y2)
  decreases y1
{
  reveal Exp_int();
  if y1 == 0 {
    assert Exp_int(x,y1) == 1;
    assert y1 + y2 == y2;
    assert Exp_int(x,y1+y2) == Exp_int(x,y2) * 1;
  } else
  if y1 == 1 {
    assert Exp_int(x,y1) == x;
  }
  else {
    // applying induction
    assert y1 > 1;
    assert y1 + y2 == 1 + ((y1 - 1) + y2);
    ExpDistributivity_int(x,1, (y1 - 1) + y2);
    ExpDistributivity_int(x,y1 - 1, y2);
  }

}


// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

lemma ModuloDistributivityMul_int(x: int, y: int, z: int)
  requires z > 0
  ensures (x * y) % z == ((x % z) * (y % z)) % z
{

  var qx := x / z;
  var rx := x % z;
  var qy := y / z;
  var ry := y % z;

  assert x == qx * z + rx;
  assert y == qy * z + ry;

  assert x * y == (qx*z + rx)*(qy*z + ry);
  assert x * y == qx*qy*z*z + qx*ry*z + qy*rx*z + rx*ry;
  calc {
    (qx*qy*z*z + qx*ry*z + qy*rx*z) % z;
  ==
    (qx*qy*z + qx*ry + qy*rx)*z % z;
  ==
    {IgnoreMod2(qx*qy*z + qx*ry + qy*rx, z);}
    0;
  }
  calc {
    x * y % z;
  ==
    (qx*qy*z*z + qx*ry*z + qy*rx*z + rx*ry ) % z;
  ==
    {
      ModuloDistributivityAdd_int(qx*qy*z*z + qx*ry*z + qy*rx*z, rx*ry, z);
    }
    ((qx*qy*z*z + qx*ry*z + qy*rx*z) % z + rx*ry % z) % z;
  ==
    (rx*ry % z) % z;
  ==
    rx*ry % z;
  }
  assert (x * y) % z == (rx * ry) % z;

  assert ((x % z) * (y % z)) % z == (rx * ry) % z;
}
    


lemma ModuloDistributivityAdd_int(a: int, b: int, z: int)
  requires z > 0
  ensures (a + b) % z == ((a % z) + (b % z)) % z
{
  // Expand a and b using quotient and remainder
  var qa := a / z;
  var ra := a % z;
  var qb := b / z;
  var rb := b % z;

  assert a == qa * z + ra;
  assert b == qb * z + rb;

  assert a + b == (qa * z + ra) + (qb * z + rb);
  assert a + b == (qa + qb) * z + (ra + rb);

  assert (a + b) % z == (ra + rb) % z by {IgnoreMod(qa+qb, ra+rb, a+b, z);}

  assert ((a % z) + (b % z)) % z == (ra + rb) % z;
}

lemma IgnoreMod2(a :int, z:nat)
  requires z > 0
  ensures (a * z) % z == 0
{
  IgnoreMod(a, 0, a*z, z);
}

lemma IgnoreMod(a: int, b:nat, c:int, z:nat)
  requires a * z + b == c
  requires z > 0
  ensures b % z == c % z
  ensures (a * z) % z == 0
{
  assert c - a*z == (b/z)*z + (b % z);
  assert (c/z)*z + (c % z) - a*z == (b/z)*z + (b % z);
  assert (c/z - a)*z + (c % z) == (b/z)*z + (b % z);
  assert (c/z - a - b/z)*z  == b % z - c % z;
  Bounding(b % z - c % z, z, c/z - a - b/z);
}
lemma Bounding(x:int, d:int, n: int)
  requires x == d * n
  requires x > -d
  requires x < d
  ensures x == 0
{}

lemma Pow2Positive(n:nat)
  ensures Pow2(n) > 0
{
  if n == 0 {
    Pow2Zero();
  }
  else {
    Pow2Positive(n-1);
    reveal Pow2();
  }
}
// The proof of Add's invariant requires a long calculation that often times
// out. To make it more robust, I've pulled it into a lemma AddAuxTop, which
// then calls 14 lemmas, one for each step of the calculation. For conciseness,
// all the lemmas use AddAuxPred as their precondition (although not all of them
// need all of AddAuxPred)

predicate AddAuxPred(x: string, y: string, oldSb: string, sb: string, oldI: int,
                     oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
{
  ValidBitString(sb) &&
  ValidBitString(x) &&
  ValidBitString(y) &&
  ValidBitString(oldSb) &&
  0 <= carry <= 1 &&
  i <= |x| - 1 && j <= |y| - 1 &&
  oldI <= |x| - 1 && oldJ <= |y| - 1 &&
  i >= -1 &&
  j >= -1 &&
  (oldI >= 0 ==> i == oldI - 1) &&
  (oldJ >= 0 ==> j == oldJ - 1) &&
  (oldI < 0 ==> i == oldI) &&
  (oldJ < 0 ==> j == oldJ) &&
  (oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)) &&
  (oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)) &&
  (oldI < 0 ==> bitX == 0) &&
  (oldJ < 0 ==> bitY == 0) &&
  |oldSb| == |sb| - 1 &&
  sum == bitX + bitY + oldCarry &&
  digit == sum % 2 &&
  carry == sum / 2 &&
  (if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
}

// Lemma 1: Apply BitStringDecomposition for both numbers
lemma AddAux1(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  BitStringDecomposition(x, oldI);
  BitStringDecomposition(y, oldJ);
}

// Lemma 2: Distribute Pow2(|oldSb|) in the third term
lemma AddAux2(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    var A := Str2Int(x[0..oldI]);
    var B := bitX;
    var C := Pow2(|oldSb|);
    Rearrange(A, B, C);
  }
}


// Lemma 3: Use associative property in the third term
lemma AddAux3(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|)) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    assert (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) == Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|)) by {
      MulIsAssociative(Str2Int(x[0..oldI]), 2, Pow2(|oldSb|));
    }
  }
}

// Lemma 4: Apply identity: 2 * Pow2(n) = Pow2(n+1) in the third term
lemma AddAux4(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|)) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  assert Pow2(|oldSb| + 1) == 2 * Pow2(|oldSb|) by {
    Pow2Inductive(|oldSb|);
  }
}

// Lemma 5: Start distributing Pow2(|oldSb|) in the fourth term
lemma AddAux5(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0)
{
  if oldJ >= 0 {
    var A := Str2Int(y[0..oldJ]);
    var B := bitY;
    var C := Pow2(|oldSb|);
    Rearrange(A, B, C);
  }
}

// Lemma 6: Use associative property in the fourth term
lemma AddAux6(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|)) + bitY * Pow2(|oldSb|) else 0)
{
  if oldJ >= 0 {
    assert (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) == Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|)) by {
      MulIsAssociative(Str2Int(y[0..oldJ]), 2, Pow2(|oldSb|));
    }
  }
}

// Lemma 7: Apply identity: 2 * Pow2(n) = Pow2(n+1) in the fourth term
lemma AddAux7(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|)) + bitY * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) + bitY * Pow2(|oldSb|) else 0)
{
  Pow2Inductive(|oldSb|);
}

// Lemma 8: Rearrange terms
lemma AddAux8(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) + bitY * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          ((oldCarry * Pow2(|oldSb|)) +
           (if oldI >= 0 then bitX else 0) * Pow2(|oldSb|)) + (if oldJ >= 0 then bitY else 0) * Pow2(|oldSb|) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  // Simple rearrangement of terms
}

// Lemma 9: Group bit terms
lemma AddAux9(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          ((oldCarry * Pow2(|oldSb|)) +
           (if oldI >= 0 then bitX else 0) * Pow2(|oldSb|)) + (if oldJ >= 0 then bitY else 0) * Pow2(|oldSb|) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          ((oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0)) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  // Grouping terms with the same factor Pow2(|oldSb|)
}

// Lemma 10: By definition of sum in the code
lemma AddAux10(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          ((oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0)) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          (sum * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  assert oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0) == sum;
}

// Lemma 11: sum = 2*carry + digit
lemma AddAux11(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (sum * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          ((2 * carry + digit) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  assert sum == 2 * carry + digit by {
    assert carry == sum / 2;
    assert digit == sum % 2;
    assert sum == (sum / 2) * 2 + (sum % 2);
  }
}

// Lemma 12: Distribute Pow2(|oldSb|)
lemma AddAux12(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          ((2 * carry + digit) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          (digit * Pow2(|oldSb|)) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  calc {
    ((2 * carry + digit) * Pow2(|oldSb|));
  ==
    2 * carry * Pow2(|oldSb|) + digit * Pow2(|oldSb|);
  ==
    {
      Pow2Inductive(|oldSb|);
    }
    (digit * Pow2(|oldSb|)) + (carry * Pow2(|oldSb| + 1));
  }
}

// Lemma 13: Definition of Str2Int for new digit + oldSb
lemma AddAux13(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (digit * Pow2(|oldSb|)) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI - 1 >= 0 then Str2Int(x[0..(oldI-1)+1]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ - 1 >= 0 then Str2Int(y[0..(oldJ-1)+1]) * Pow2(|oldSb| + 1) else 0)
{
  PrependDigitToString(digit, oldSb);
}

// Lemma 14: By definition of sb and updated i, j
lemma AddAux14(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI - 1 >= 0 then Str2Int(x[0..(oldI-1)+1]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ - 1 >= 0 then Str2Int(y[0..(oldJ-1)+1]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(sb) +
          (carry * Pow2(|sb|)) +
          (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
          (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
  assert Pow2(|sb|) == Pow2(|oldSb| + 1);
  assert (if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb;

  if oldI >= 0 {
    assert i == oldI - 1;
    if i >= 0 {
      assert x[0..i+1] == x[0..oldI];
    }
  }

  if oldJ >= 0 {
    assert j == oldJ - 1;
    if j >= 0 {
      assert y[0..j+1] == y[0..oldJ];
    }
  }
}

// Top-level lemma that combines all the individual steps
lemma AddAuxTop(x: string, y: string, oldSb: string, sb: string, oldI: int,
                oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          Str2Int(sb) +
          (carry * Pow2(|sb|)) +
          (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
          (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
  // Call all the sub-lemmas in sequence to establish the proof
  AddAux1(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux2(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux3(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux4(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux5(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux6(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux7(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux8(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux9(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux10(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux11(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux12(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux13(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux14(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
}
// The next few lemmas will be needed
// at various steps in the main proofs

lemma IgnoreInitialZeros(s : string, numZeros:int)
  requires ValidBitString(s)
  requires 0<=numZeros<=|s|
  requires forall i :: 0<=i<numZeros ==> s[i] == '0'
  ensures Str2Int(s) == Str2Int(s[numZeros..])
{
  if numZeros == 0 {
    return;
  }
  if numZeros == |s| {
    assert Str2Int(s) == (2 * Str2Int(s[0..|s|-1]));
    IgnoreInitialZeros(s[..|s|-1], numZeros-1);
    return;
  }
  IgnoreInitialZeros(s[..|s|-1], numZeros);
  var t := s[numZeros..];
  calc {
    Str2Int(s);
  ==
    (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  ==
    (2 * Str2Int(s[numZeros..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  ==
    {
      assert t[..|t|-1] == s[numZeros..|s|-1];
      assert t[|t|-1] == s[|s|-1];
    }
    (2 * Str2Int(t[..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0));
  ==
    Str2Int(t);
  }
}


// Claude was able to mostly prove this one via calc.
// I wonder if it could be slightly easier to read by
// defining t := s[0..i+1] and expanding Str2Int(t)
lemma BitStringDecomposition(s: string, i: int)
  requires ValidBitString(s) && i < |s|
  ensures i >= 0 ==> Str2Int(s[0..i+1]) == Str2Int(s[0..i]) * 2 + (if s[i] == '1' then 1 else 0)
{
  if i >= 0 {
    calc {
      Str2Int(s[0..i+1]);
    == // By definition of Str2Int
      if |s[0..i+1]| == 0 then 0
      else (2 * Str2Int(s[0..i+1][0..|s[0..i+1]|-1]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0));
    == // Since i >= 0, |s[0..i+1]| = i+1 > 0
      2 * Str2Int(s[0..i+1][0..|s[0..i+1]|-1]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    == // Simplify: s[0..i+1][0..|s[0..i+1]|-1] = s[0..i+1][0..i] = s[0..i]
      2 * Str2Int(s[0..i+1][0..i]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    ==
      { assert  s[0..i+1][0..i] == s[0..i];}
      2 * Str2Int(s[0..i]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    ==
      2 * Str2Int(s[0..i]) + (if s[0..i+1][i] == '1' then 1 else 0);
    == // Simplify: s[0..i+1][i] = s[i]
      2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
    }
  }
}



lemma PrependDigitToString(digit: int, s: string)
  requires ValidBitString(s) && (digit == 0 || digit == 1)
  ensures Str2Int(if digit == 1 then ['1'] + s else ['0'] + s) ==
          Str2Int(s) + digit * Pow2(|s|)
{
  reveal Pow2();
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant Str2Int(if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]) == Str2Int(s[..i]) + digit * Pow2(|s[..i]|)
  {
    var t := if digit == 1 then ['1'] + s[..i+1] else ['0'] + s[..i+1];
    calc {
      Str2Int(t);
    ==
      if |t| == 0 then  0  else  (2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0));
    ==
      {assert |t| != 0;}
      2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    ==
      {
        assert t[|t|-1] == s[i];
        assert t[0..|t|-1] == (if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]);
      }
      2 * Str2Int(if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]) + (if s[i] == '1' then 1 else 0);
    ==
      2 * (Str2Int(s[..i]) + digit * Pow2(|s[..i]|)) + (if s[i] == '1' then 1 else 0);
    ==
      {
        var u := s[..i+1];
        calc {
          2 * Str2Int(s[..i]) + (if s[i] == '1' then 1 else 0);
        ==
          { assert s[..i] == u[0..|u|-1];
            assert s[i] == u[|u|-1];
          }
          2 * Str2Int(u[0..|u|-1]) + (if u[|u|-1] == '1' then 1 else 0);
        ==
          Str2Int(s[..i+1]);
        }
      }
      Str2Int(s[..i+1]) + digit * Pow2(|s[..i+1]|);
    }

    i:= i+1;
  }
  assert s[..i] == s;
}


lemma Bound(s : string)
  requires ValidBitString(s)
  ensures Pow2(|s|) > Str2Int(s)
{
  if |s| == 0 {
    Pow2Zero();
  }
  else {
    calc {
      Str2Int(s);
    ==
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    <=
      {Bound(s[0..|s|-1]);}
      2 * (Pow2(|s[0..|s|-1]|)-1) + (if s[|s|-1] == '1' then 1 else 0);
    ==
      2 * Pow2(|s|-1) - 2  + (if s[|s|-1] == '1' then 1 else 0);
    <=
      2 * Pow2(|s|-1) - 1;
    ==
      {Pow2Inductive(|s|-1);}
      Pow2(|s|) - 1;
    <
      Pow2(|s|);
    }
  }

}

lemma TrailingZeros(s: string, numZeros: nat)
  requires ValidBitString(s)
  requires numZeros <= |s|
  requires forall i :: |s| - numZeros <= i < |s| ==> s[i] == '0'
  ensures Str2Int(s) == Str2Int(s[..|s|-numZeros]) * Pow2(numZeros)
{
  if numZeros == 0 {
    calc {
      OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros);
    ==
      {Pow2Zero();}
      OStr2Int(s[..|s|]) * 1;
    ==
      {assert s[..|s|] == s;}
      OStr2Int(s);
    }
    reveal OStr2Int;
    return;
  }
  calc {
    OStr2Int(s);
  ==
    {reveal OStr2Int;}
    2 * OStr2Int(s[..|s|-1]);
  ==
    {TrailingZeros(s[..|s|-1], numZeros-1);
     assert s[..|s|-1][..|s|-numZeros] == s[..|s|-numZeros];
     reveal OStr2Int;
    }
    2 * (OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros-1));
  ==
    OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros-1) * 2;
  ==
    OStr2Int(s[..|s|-numZeros]) * (Pow2(numZeros-1) * 2);
  ==
    {
      Pow2Inductive(numZeros-1);
    }
    OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros);
  }
  reveal OStr2Int;
}

// The next few lemmas are trivial, but they're useful when Dafny struggles with
// algebra in complicated expressions

lemma MulIsAssociative(a: nat, b: nat, c: nat)
  ensures a * (b * c) == a * b * c
{
}


lemma Expand(A:nat, B:nat, C:nat)
  ensures A * (B + 1) * C == A * C + A * B * C
{
}

lemma Rearrange(A:int, B:int, C:int)
  ensures (A * 2 + B) * C == A * 2 * C + B * C
{
}
// Below is a Dafny program that:

// - Represents natural numbers as binary strings consisting only of `'0'` and `'1'`.
// - Has two **conversion** functions, defined in bitstrings.dfy
//   1. `Str2Int(s)`: Convert a valid bit-string `s` into a natural number.
//   2. `Int2Str(n)`: Convert a natural number `n` into its binary representation (with no leading zeros except if `n = 0`).
//
// - Has three **pure string-based** arithmetic methods, each **not** using `Str2Int` or `Int2Str` inside the method body:
// 1. `Add(s1, s2)`: Returns the bit-string representing the sum of `s1` and `s2`.
// 2. `Sub(s1, s2)`: Returns the bit-string representing `s1 - s2`, assuming `s1 >= s2`.
//  3. `Mul(s1, s2)`: Returns the bit-string representing the product `s1 * s2`.
//
// All methods come with specifications ensuring they do what they claim, and we prove correctness using Dafny's function specifications (`ensures`) by comparing the result against the reference functions `Str2Int` and `Int2Str`.

// Note: To check that Add/Sub/Mul only use Int2Str and Str2Int for verification:
// 1. Change Int2Str, OStr2Int, and Str2Int to `ghost function`
// 2. Delete Main (because it uses Int2Str/Str2Int in executable code, so now won't verify)
// 3. The rest of the code will still verify




method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  // First pass: keep only valid bits
  var validBits := "";
  var i := 0;
  while i < |s|
    invariant ValidBitString(validBits)
    invariant 0 <= i <= |s|
    invariant i >= |validBits|
    invariant |s| >= |validBits|
    invariant ValidBitString(s) ==> i == |validBits|
    invariant ValidBitString(s) ==> s[..i] == validBits[..i]
  {
    if s[i] == '0' || s[i] == '1' {
      validBits := validBits + [s[i]];
    }
    i := i + 1;
  }
  assert ValidBitString(s) ==> s == validBits;
  assert ValidBitString(validBits);
  // Second pass: remove leading zeros
  var j := 0;
  assert ValidBitString(s) ==> Str2Int(s[j..]) == Str2Int(s);
  while j < |validBits| && validBits[j] == '0'
    invariant j <= |validBits|
    invariant forall idx :: 0 <= idx < j ==> validBits[idx] == '0'
  {
    j := j + 1;
  }
  if ValidBitString(s){
    assert Str2Int(s[j..]) == Str2Int(s) by
    {
      IgnoreInitialZeros(s, j);
    }
  }

  // Extract substring after leading zeros
  if j == |validBits| {
    // All zeros or empty
    return "0";
  }
  assert j <= |validBits|;
  return validBits[j..];
}


// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // We implement classic binary addition from right to left.
  // Step 1: Normalize inputs (drop leading zeros if needed).
  var x := NormalizeBitString(s1);
  var y := NormalizeBitString(s2);

  if y == "0" {
    res := x;
    return;
  }

  // We build the result from the least significant bit forward.
  var i := |x| - 1;  // index on x
  var j := |y| - 1;  // index on y
  var carry := 0;
  var sb := []; // dynamic seq of chars for result (in reverse order)

  assert x[0..i+1] == x;
  assert y[0..j+1] == y;
  assert Str2Int(x) + Str2Int(y) ==
         (if i >= 0 then Str2Int(x[0..i+1]) else 0) +
         (if j >= 0 then Str2Int(y[0..j+1]) else 0);

  Pow2Zero();
  while i >= 0 || j >= 0 || carry != 0
    decreases i + j + 2, carry
    invariant 0 <= carry <= 1
    invariant i <= |x| - 1 && j <= |y| - 1
    invariant i >= -1
    invariant j >= -1
    invariant ValidBitString(sb)
    invariant Str2Int(x) + Str2Int(y) ==
              Str2Int(sb) +
              (carry * Pow2(|sb|)) +
              (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
              (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
  {
    var oldSb := sb;
    var oldCarry := carry;
    var bitX := 0;
    if i >= 0 {
      bitX := if x[i] == '1' then 1 else 0;
    }
    var bitY := 0;
    if j >= 0 {
      bitY := if y[j] == '1' then 1 else 0;
    }

    var sum := bitX + bitY + carry;
    var digit := sum % 2;
    carry := sum / 2;

    if digit == 1 {
      sb := ['1'] + sb;
    }
    else
    {
      sb := ['0'] + sb;
    }

    var oldI := i;
    var oldJ := j;

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }

    AddAuxTop(x, y, oldSb, sb, oldI,
              oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  }

  assert Str2Int(x) + Str2Int(y) == Str2Int(sb);

  res := NormalizeBitString(sb);

  assert Str2Int(sb) == Str2Int(res);

  return res;
}


// ----------------------------------------------------
// string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  var x := NormalizeBitString(s1);
  var y := NormalizeBitString(s2);

  // If y == "0", the difference is x
  if y == "0" {
    res := x;
    return;
  }
  // If x == y, the difference is "0"
  if x == y {
    res := "0";
    return;
  }

  var i := |x| - 1; // pointer on x
  var j := |y| - 1; // pointer on y
  var borrow := 0;
  var sb := [];

  Pow2Zero();
  assert borrow * Pow2(|sb|) == 0;
  calc {
    if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0;
  ==
    Str2Int(x[0..i+1]) * Pow2(|sb|);
  ==
    Str2Int(x[0..i+1]) * 1;
  ==
    Str2Int(x[0..i+1]);
  ==
    {assert x[0..i+1] == x;}
    Str2Int(x);
  }
  calc {
    if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0;
  ==
    Str2Int(y[0..j+1]) * Pow2(|sb|);
  ==
    Str2Int(y[0..j+1]) * 1;
  ==
    Str2Int(y[0..j+1]);
  ==
    {assert y[0..j+1] == y;}
    Str2Int(y);
  }

  while i >= 0 || j >= 0
    decreases i + j + 2, borrow
    invariant 0 <= borrow <= 1
    invariant i <= |x| - 1 && j <= |y| - 1
    invariant i >= -1
    invariant j >= -1
    invariant ValidBitString(sb)
    invariant Str2Int(x) - Str2Int(y) ==
              Str2Int(sb) -
              (borrow * Pow2(|sb|)) +
              (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) -
              (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
  {
    var oldSb := sb;
    var oldBorrow := borrow;
    var bitX := 0;
    if i >= 0 {
      bitX := if x[i] == '1' then 1 else 0;
    }
    var bitY := 0;
    if j >= 0 {
      bitY := if y[j] == '1' then 1 else 0;
    }

    // Subtract with borrow:
    var rawDiff := bitX - bitY - borrow;
    var diff := rawDiff;
    if rawDiff < 0 {
      diff := rawDiff + 2;
      borrow := 1;
    } else {
      borrow := 0;
    }

    assert diff == 1 || diff == 0;
    if diff == 1 {
      sb := ['1'] + sb;
    } else {
      sb := ['0'] + sb;
    }

    var oldI := i;
    var oldJ := j;

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }

    SubAuxTop(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
    reveal OStr2Int;
  }



  // If borrow is 1, the RHS will be negative,
  // but the LHS is nonnegative
  assert Str2Int(x) - Str2Int(y) == Str2Int(sb) - (borrow * Pow2(|sb|));
  assert Pow2(|sb|) > Str2Int(sb) by {Bound(sb);}
  assert borrow == 0;


  assert Str2Int(x) - Str2Int(y) == Str2Int(sb);

  res := NormalizeBitString(sb);

  assert Str2Int(sb) == Str2Int(res);
}



// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var x := NormalizeBitString(s1);
  var y := NormalizeBitString(s2);

  // If either is "0", result is "0"
  if x == "0" || y == "0" {
    res := "0";
    return;
  }

  // We'll implement the classic method:
  //   product = 0
  //   for each bit of y (from right to left):
  //       if that bit == 1, add (x << position) to product
  // Use Add(...) to accumulate partial sums.

  var product := "0";
  var shift := "";
  var idx := |y| - 1;
  calc {
    OStr2Int(x) * OStr2Int(y);
  ==
    {
      assert OStr2Int(product) == 0 by {reveal OStr2Int;}
      assert y[..idx+1] + shift == y;
      assert OStr2Int(y[..idx+1] + shift) == OStr2Int(y);
    }
    OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
  }
  while idx >= 0
    decreases idx
    invariant -1 <= idx < |y|
    invariant ValidBitString(y[..idx+1] + shift)
    invariant ValidBitString(product)
    invariant ValidBitString(shift)
    invariant forall i :: 0<=i<|shift| ==> shift[i] == '0'
    invariant OStr2Int(x) * OStr2Int(y) == OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift)
  {
    var prevProduct := product;
    var prevIdx := idx;
    var prevShift := shift;
    if y[idx] == '1' {
      var partial := x + shift;
      product := Add(product, partial);
      assert OStr2Int(product) == OStr2Int(prevProduct)+ OStr2Int(x + prevShift) by {reveal OStr2Int;}
    }
    shift := shift + ['0'];
    idx := idx - 1;
    assert ValidBitString(y[..idx+1] + shift);

    // Use the MulAux lemma to maintain the loop invariant
    MulAux(x, y, prevProduct, product, prevShift, shift, idx);
  }
  assert idx == -1;
  calc {
    OStr2Int(x) * OStr2Int(y);
  ==
    OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
  ==
    { assert y[..idx+1] == "";
      assert y[..idx+1] + shift == shift;
    }
    OStr2Int(product) + OStr2Int(x) * OStr2Int(shift);
  ==
    {reveal OStr2Int;
     IgnoreInitialZeros(shift, |shift|);}
    OStr2Int(product);
  }
  assert Str2Int(x) * Str2Int(y) == Str2Int(product) by {reveal OStr2Int;}
  res := product;
}

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}


// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}
// Helper lemma for maintaining the loop invariant in Mul
lemma MulAux(x: string, y: string, prevProduct: string, product: string,
             prevShift: string, shift: string, idx: int)
  requires ValidBitString(x) && ValidBitString(y)
  requires ValidBitString(prevProduct) && ValidBitString(product)
  requires ValidBitString(prevShift) && ValidBitString(shift)
  requires -1 <= idx < |y| - 1
  requires forall i :: 0 <= i < |prevShift| ==> prevShift[i] == '0'
  requires forall i :: 0 <= i < |shift| ==> shift[i] == '0'
  requires shift == prevShift + ['0']
  requires idx + 1 < |y|
  requires y[idx+1] == '0' ==> prevProduct == product
  requires y[idx+1] == '1' ==> OStr2Int(product) == OStr2Int(prevProduct)+ OStr2Int(x + prevShift)
  requires OStr2Int(x) * OStr2Int(y) == OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift)
  ensures OStr2Int(x) * OStr2Int(y) ==
          OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift) ==>
            OStr2Int(x) * OStr2Int(y) ==
            OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift)
{
  if y[idx+1] == '0' {
    calc {
      OStr2Int(x) * OStr2Int(y);
    ==
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift);
    ==
      {
        assert prevProduct == product;
        assert y[..idx+2] + prevShift == y[..idx+1] + shift;
      }
      OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
    }
  }
  else {
    var a := |shift|;
    calc {
      OStr2Int(x) * OStr2Int(y);
    ==
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift);
    ==
      { assert y[..idx+2] + prevShift == y[..idx+1] + "1" + prevShift;}
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift);
    ==
      { TrailingZeros(y[..idx+1] + "1" + prevShift, a-1);
        assert OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(y[..idx+1] + "1") * Pow2(a-1) by {reveal OStr2Int;}
        assert OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(x) * (OStr2Int(y[..idx+1] + "1") * Pow2(a-1));
        assert OStr2Int(x) * (OStr2Int(y[..idx+1] + "1") * Pow2(a-1)) == OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1)
        by {MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1] + "1"), Pow2(a-1));}

        assert OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1);
      }
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1);
    ==
      {reveal OStr2Int;
      }
      OStr2Int(prevProduct) + OStr2Int(x) * (2*OStr2Int(y[..idx+1]) + 1) * Pow2(a-1);
    ==
      {
        Expand(OStr2Int(x), 2*OStr2Int(y[..idx+1]), Pow2(a-1));
      }
      OStr2Int(prevProduct) + OStr2Int(x) * Pow2(a-1) + OStr2Int(x) * (2*OStr2Int(y[..idx+1])) * Pow2(a-1);
    ==
      {assert OStr2Int(x) * Pow2(a-1) == OStr2Int(x + prevShift) by {

         reveal OStr2Int;
         TrailingZeros(x+ prevShift, a-1);
       }
       calc {
         OStr2Int(x) * (2*OStr2Int(y[..idx+1])) * Pow2(a-1);
       ==
         {
           MulIsAssociative(OStr2Int(x), 2*OStr2Int(y[..idx+1]), Pow2(a-1));
         }
         OStr2Int(x) * ((2*OStr2Int(y[..idx+1])) * Pow2(a-1));
       ==
         {
           assert (2*OStr2Int(y[..idx+1])) * Pow2(a-1) == OStr2Int(y[..idx+1]) * Pow2(a)
           by{
             Pow2Inductive(a-1);
           }
         }
         OStr2Int(x) * (OStr2Int(y[..idx+1]) * Pow2(a));
       ==
         {MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1]), Pow2(a));}
         OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a);
       }
      }
      OStr2Int(prevProduct) + OStr2Int(x + prevShift) + OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a);
    ==
      {
        assert OStr2Int(y[..idx+1]) * Pow2(a) ==  OStr2Int(y[..idx+1] + shift) by {
          reveal OStr2Int;
          TrailingZeros(y[..idx+1] + shift, a);
        }
        MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1]), Pow2(a));
        assert OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a) ==  OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
      }
      OStr2Int(prevProduct) + OStr2Int(x + prevShift) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
    ==
      {reveal OStr2Int;}
      OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
    }
  }
}

// This function will be useful in proofs
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Establish some properties of Pow2
lemma Pow2Zero()
  ensures Pow2(0) == 1
{
  reveal Pow2();
}

lemma Pow2Inductive(i: nat)
  ensures Pow2(i+1) == 2*Pow2(i)
{
  reveal Pow2();
}
// Sub also has a long calculation step, which again we split into a bunch of lemmas

predicate SubAuxPred(x: string, y: string, oldSb: string, sb: string, oldI: int,
                     oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
{
  ValidBitString(sb) &&
  ValidBitString(x) &&
  ValidBitString(y) &&
  ValidBitString(oldSb) &&
  0 <= borrow <= 1 &&
  i <= |x| - 1 && j <= |y| - 1 &&
  oldI <= |x| - 1 && oldJ <= |y| - 1 &&
  i >= -1 &&
  j >= -1 &&
  (oldI >= 0 ==> i == oldI - 1) &&
  (oldJ >= 0 ==> j == oldJ - 1) &&
  (oldI < 0 ==> i == oldI) &&
  (oldJ < 0 ==> j == oldJ) &&
  (oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)) &&
  (oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)) &&
  (oldI < 0 ==> bitX == 0) &&
  (oldJ < 0 ==> bitY == 0) &&
  |oldSb| == |sb| - 1 &&
  (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb &&
  ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff &&
  (rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1) &&
  (rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0)
}

// Lemma 1: Apply BitStringDecomposition for both numbers
lemma SubAux1(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then (OStr2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then (OStr2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  reveal OStr2Int;
  BitStringDecomposition(x, oldI);
  BitStringDecomposition(y, oldJ);
}

// Lemma 2: Distribute Pow2(|oldSb|)
lemma SubAux2(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then (OStr2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then (OStr2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * 2 * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * 2 * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    assert (OStr2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) == OStr2Int(x[0..oldI]) * 2 * Pow2(|oldSb|) + bitX * Pow2(|oldSb|);
  }
  if oldJ >= 0 {
    var A := OStr2Int(y[0..oldJ]);
    var B := bitY;
    var C := Pow2(|oldSb|);
    Rearrange(A, B, C);
  }
}

// Lemma 3: Use Pow2 relationship: 2 * Pow2(n) = Pow2(n+1)
lemma SubAux3(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * 2 * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * 2 * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) + bitY * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    var A := OStr2Int(x[0..oldI]);
    var B := Pow2(|oldSb|);
    assert (A * 2) * B == A * (2 * B) by { MulIsAssociative(A, 2, B); }
    Pow2Inductive(|oldSb|);
    assert Pow2(|oldSb|+1) == 2 * Pow2(|oldSb|);
  }

  if oldJ >= 0 {
    var A := OStr2Int(y[0..oldJ]);
    var B := Pow2(|oldSb|);
    assert (A * 2) * B == A * (2 * B) by { MulIsAssociative(A, 2, B); }
    Pow2Inductive(|oldSb|);
    assert Pow2(|oldSb|+1) == 2 * Pow2(|oldSb|);
  }
}

// Lemma 4: Rearrange to isolate the digit contribution
lemma SubAux4(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) + bitY * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) * Pow2(|oldSb|)
{
  // Rearrangement step - just algebraic manipulation
}

// Lemma 5: By the definition of diff in code
lemma SubAux5(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) * Pow2(|oldSb|) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (rawDiff * Pow2(|oldSb|))
{
  assert ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff;
}

// Lemma 6: Apply relationship between rawDiff, diff and borrow
lemma SubAux6(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (rawDiff * Pow2(|oldSb|)) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if rawDiff < 0 then diff - 2 else diff) * Pow2(|oldSb|))
{
  if rawDiff < 0 {
    assert rawDiff + 2 == diff;
    assert borrow == 1;
    assert rawDiff == diff - 2;
  } else {
    assert rawDiff == diff;
    assert borrow == 0;
  }
}

// Lemma 7: Rewrite in terms of borrow
lemma SubAux7(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if rawDiff < 0 then diff - 2 else diff) * Pow2(|oldSb|)) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (if borrow == 1 then 2 * Pow2(|oldSb|) else 0))
{
  // Rewrite using borrow
}

// Lemma 8: Use Pow2 relationship again
lemma SubAux8(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (if borrow == 1 then 2 * Pow2(|oldSb|) else 0)) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (borrow * Pow2(|oldSb|+1)))
{
  if borrow == 1 {
    assert 2 * Pow2(|oldSb|) == Pow2(|oldSb|+1) by { Pow2Inductive(|oldSb|); }
  }
}

// Lemma 9: Rearrange terms
lemma SubAux9(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (borrow * Pow2(|oldSb|+1))) ==
          OStr2Int(oldSb) +
          diff * Pow2(|oldSb|) +
          (if i >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if j >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) -
          (borrow * Pow2(|oldSb|+1))
{
  reveal OStr2Int;
}

// Lemma 10: Apply PrependDigitToString
lemma SubAux10(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) +
          diff * Pow2(|oldSb|) +
          (if i >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if j >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) -
          (borrow * Pow2(|oldSb|+1)) ==
          OStr2Int(if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) +
          (if i >= 0 then OStr2Int(x[0..i+1]) * Pow2(|oldSb|+1) else 0) -
          (if j >= 0 then OStr2Int(y[0..j+1]) * Pow2(|oldSb|+1) else 0) -
          (borrow * Pow2(|oldSb|+1))
{
  // Apply PrependDigitToString to convert the expression
  reveal OStr2Int;
  PrependDigitToString(diff, oldSb);

  // Establish that sb == (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb)
  assert sb == (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb);

  // Establish relationships between indices when working with slices
  if i >= 0 {
    assert oldI >= 0 && i == oldI - 1;
    assert x[0..i+1] == x[0..oldI];  // Since i+1 == oldI
  }

  if j >= 0 {
    assert oldJ >= 0 && j == oldJ - 1;
    assert y[0..j+1] == y[0..oldJ];  // Since j+1 == oldJ
  }
}



// Top-level lemma that combines all the individual steps
lemma SubAuxTop(x: string, y: string, oldSb: string, sb: string, oldI: int,
                oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          OStr2Int(sb) -
          (borrow * Pow2(|sb|)) +
          (if i >= 0 then OStr2Int(x[0..i+1]) * Pow2(|sb|) else 0) -
          (if j >= 0 then OStr2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
  // Call all the sub-lemmas in sequence to establish the proof
  SubAux1(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux2(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux3(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux4(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux5(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux6(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux7(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux8(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux9(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux10(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);

}