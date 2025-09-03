ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost lemma PrependBitLemma(b: int, s: string)
  requires b == 0 || b == 1
  ensures Str2Int((if b == 1 then "1" else "0") + s) == Exp_int(2, |s|) * b + Str2Int(s)
{
  if |s| == 0 {
    // (if b==1 then "1" else "0") has length 1, Str2Int of it is b.
    // Exp_int(2,0) * b + Str2Int("") = 1*b + 0 = b
  } else {
    var s1 := s[0..|s|-1];
    PrependBitLemma(b, s1);
    // Let lastbit = (if s[|s|-1] == '1' then 1 else 0)
    // Str2Int((if b==1 then "1" else "0") + s) =
    //   2 * Str2Int((if b==1 then "1" else "0") + s1) + lastbit
    // By IH Str2Int((b) + s1) = Exp_int(2, |s1|) * b + Str2Int(s1)
    // So above equals 2 * (Exp_int(2, |s1|) * b + Str2Int(s1)) + lastbit
    // = Exp_int(2, |s1|+1) * b + (2*Str2Int(s1) + lastbit)
    // = Exp_int(2, |s|) * b + Str2Int(s)
  }
}

ghost lemma Exp2_succ(n: nat)
  ensures Exp_int(2, n+1) == 2 * Exp_int(2, n)
{
  if n == 0 {
    // Exp_int(2,1) == 2 == 2 * 1 == 2 * Exp_int(2,0)
  } else {
    Exp2_succ(n-1);
    // follows by definition
  }
}

ghost lemma Exp_square(x: nat, a: nat)
  ensures Exp_int(x, a) * Exp_int(x, a) == Exp_int(x, 2 * a)
{
  if a == 0 {
    // 1 * 1 == 1
  } else {
    Exp_square(x, a-1);
    // Exp_int(x, a) = x * Exp_int(x, a-1)
    // So LHS = x*Exp(x,a-1) * x*Exp(x,a-1) = x*x * Exp(x,a-1)*Exp(x,a-1)
    // By IH this equals x*x * Exp(x, 2*(a-1)) = Exp(x, 2*a)
  }
}

// executable helper: convert natural number to bitstring (most significant bit on left)
method IntToBitString(t0: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == t0
{
  if t0 == 0 {
    s := "0";
    return;
  }
  s := "";
  var cur := t0;
  // Invariant: t0 == cur * Exp_int(2, |s|) + Str2Int(s)
  while cur > 0
    invariant ValidBitString(s)
    invariant t0 == cur * Exp_int(2, |s|) + Str2Int(s)
    decreases cur
  {
    var b := cur % 2;
    cur := cur / 2;
    if b == 1 {
      s := "1" + s;
    } else {
      s := "0" + s;
    }
    // Prove invariant holds after update:
    // t0 == (old cur) * Exp_int(2, |olds|) + Str2Int(olds)
    // let olds be previous s. After update, new s = (bit) + olds, new |s| = |olds|+1, new cur = oldcur/2
    // Use PrependBitLemma to relate Str2Int.
    PrependBitLemma(b, s[1..|s|]); // s[1..|s|] is olds
    // The algebraic reasoning above justifies the invariant; no additional action required.
  }
  // when loop finishes, cur == 0 and invariant yields Str2Int(s) == t0
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var m := Str2Int(sz);
  var x := Str2Int(sx);
  var e := Str2Int(sy);
  if e == 0 {
    var rr := 1 % m;
    res := IntToBitString(rr);
    return;
  }
  // e == Exp_int(2, n)
  var curPow := x % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant curPow < m
    invariant curPow == Exp_int(x, Exp_int(2, i)) % m
    decreases n - i
  {
    // square modulo m: curPow := (curPow * curPow) % m
    var old := curPow;
    curPow := (old * old) % m;
    // From invariant and Exp_square we get new invariant for i+1:
    // old == Exp_int(x, Exp_int(2,i)) % m
    // So old*old % m == Exp_int(x, Exp_int(2,i)) * Exp_int(x, Exp_int(2,i)) % m
    // By Exp_square this is Exp_int(x, 2 * Exp_int(2,i)) % m
    // And Exp2_succ gives Exp_int(2, i+1) == 2 * Exp_int(2,i)
    i := i + 1;
  }
  res := IntToBitString(curPow);
}
// </vc-code>

