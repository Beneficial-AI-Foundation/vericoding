// <vc-preamble>
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)

  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  assume{:axiom} false;
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
lemma Str2Int_AllZero(s: string)
  requires ValidBitString(s)
  ensures AllZero(s) <==> Str2Int(s) == 0
  decreases |s|
{
  if |s| > 0 {
    Str2Int_AllZero(s[0..|s|-1]);
  }
}

lemma NotAllZeroAndLengthOne(s: string)
  requires ValidBitString(s) && |s| == 1 && !AllZero(s)
  ensures s == "1"
{
}

/* helper modified by LLM (iteration 5): Rewrote inductive proof to be more explicit to avoid timeout. */
lemma LemmaModPlusCongruence(k: nat, c: nat, n: nat)
  requires n > 0
  ensures (k * n + c) % n == c % n
  decreases k
{
  if k > 0 {
    LemmaModPlusCongruence(k - 1, c, n);
    var prev := (k - 1) * n + c;
    calc == {
      (prev + n) % n;
      (prev % n + n % n) % n;
      (prev % n + 0) % n;
      (prev % n) % n;
      prev % n;
    }
    calc == {
      (k * n + c) % n;
      ((k - 1) * n + n + c) % n;
      (prev + n) % n;
      prev % n;
      c % n;
    }
  }
}

/* helper modified by LLM (iteration 2): added proof to prevent timeout */
lemma ModMul(a: nat, b: nat, n: nat)
  requires n > 0
  ensures (a * b) % n == ((a % n) * (b % n)) % n
{
  var ra := a % n;
  var rb := b % n;

  // Prove (a*b)%n == (ra*b)%n
  assert a == (a/n)*n + ra;
  assert a * b == (a/n)*b*n + ra*b;
  LemmaModPlusCongruence((a/n)*b, ra*b, n);
  assert (a * b) % n == (ra*b) % n;

  // Prove (ra*b)%n == (ra*rb)%n
  assert b == (b/n)*n + rb;
  assert ra*b == ra*(b/n)*n + ra*rb;
  LemmaModPlusCongruence(ra*(b/n), ra*rb, n);
  assert (ra*b)%n == (ra*rb)%n;
  
  // Combine
  assert (a*b)%n == (ra*rb)%n;
  assert (a*b)%n == ((a%n)*(b%n))%n;
}

lemma Exp_distr(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
  decreases y2
{
  if y2 > 0 {
    Exp_distr(x, y1, y2 - 1);
  }
}

lemma Exp_sq(x: nat, y: nat)
  ensures Exp_int(x, 2*y) == Exp_int(x, y) * Exp_int(x, y)
{
  Exp_distr(x, y, y);
}

lemma Str2Int_shr(s: string)
    requires |s| > 0 && ValidBitString(s)
    ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + if s[|s|-1] == '1' then 1 else 0
{
}

// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)

  requires |sy| > 0 && Str2Int(sz) > 1
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): No change needed, the fix in the helpers should resolve verification. */
  Str2Int_AllZero(sy);
  if AllZero(sy) {
    res := "1";
    return;
  }

  if |sy| == 1 {
    NotAllZeroAndLengthOne(sy);
    var quot: string;
    quot, res := DivMod(sx, sz);
    return;
  }

  var sy_prime := sy[0..|sy|-1];
  assert |sy_prime| > 0;
  
  var rec_res := ModExp(sx, sy_prime, sz);
  
  ghost var x := Str2Int(sx);
  ghost var z := Str2Int(sz);
  ghost var y_prime_val := Str2Int(sy_prime);
  
  Exp_sq(x, y_prime_val);
  ModMul(Exp_int(x, y_prime_val), Exp_int(x, y_prime_val), z);

  var temp_res_sq := Mul(rec_res, rec_res);
  var r_sq: string;
  var r_sq_q: string;
  r_sq_q, r_sq := DivMod(temp_res_sq, sz);

  Str2Int_shr(sy);
  if sy[|sy|-1] == '0' {
    res := r_sq;
  } else {
    ghost var exp_sq_val := Exp_int(x, y_prime_val) * Exp_int(x, y_prime_val);
    ModMul(exp_sq_val, x, z);
    
    var sx_mod_sz_r: string;
    var sx_mod_sz_q: string;
    sx_mod_sz_q, sx_mod_sz_r := DivMod(sx, sz);
    
    var final_prod := Mul(r_sq, sx_mod_sz_r);
    var final_res_q: string;
    final_res_q, res := DivMod(final_prod, sz);
  }
}

// </vc-code>
