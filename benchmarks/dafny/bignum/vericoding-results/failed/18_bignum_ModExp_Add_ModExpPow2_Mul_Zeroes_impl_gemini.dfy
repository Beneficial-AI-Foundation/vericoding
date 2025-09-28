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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): added lemma_ModPlus to assist proof of lemma_ModMul */
lemma lemma_ModPlus(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a + b * m) % m == a % m
{
}

/* helper modified by LLM (iteration 10): simplified proof of lemma_ModMul using lemma_ModPlus to resolve timeout */
lemma lemma_ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  calc {
    (a * b) % m;
    == (a * ((b/m)*m + b%m)) % m;
    == (a*(b/m)*m + a*(b%m)) % m;
    == { lemma_ModPlus(a*(b%m), a*(b/m), m); }
       (a * (b%m)) % m;
    == (((a/m)*m + a%m) * (b%m)) % m;
    == ((a/m)*m*(b%m) + (a%m)*(b%m)) % m;
    == { lemma_ModPlus((a%m)*(b%m), (a/m)*(b%m), m); }
       ((a%m)*(b%m)) % m;
  }
}

lemma lemma_Exp_add(a: nat, b: nat, c: nat)
  decreases c
  ensures Exp_int(a, b + c) == Exp_int(a, b) * Exp_int(a, c)
{
  if c > 0 {
    lemma_Exp_add(a, b, c - 1);
  }
}

lemma lemma_Exp_2p(a: nat, b: nat)
  ensures Exp_int(a, 2*b) == Exp_int(a,b) * Exp_int(a,b)
{
  lemma_Exp_add(a, b, b);
}

method ModExpRecursive(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases |sy|
{
  if |sy| == 0 {
    return "1";
  } else {
    var sy_prime := sy[0..|sy|-1];
    var last_bit := sy[|sy|-1];

    var rec_res := ModExpRecursive(sx, sy_prime, sz);

    var sq_term_str := Mul(rec_res, rec_res);
    var mod_sq_term := ModExpPow2(sq_term_str, "1", 0, sz);
    
    var x := Str2Int(sx);
    var y_prime := Str2Int(sy_prime);
    var z := Str2Int(sz);
    
    if last_bit == '0' {
      lemma_Exp_2p(x, y_prime);
      lemma_ModMul(Exp_int(x, y_prime), Exp_int(x, y_prime), z);
      return mod_sq_term;
    } else { // last_bit == '1'
      lemma_Exp_2p(x, y_prime);
      lemma_ModMul(Exp_int(x, y_prime), Exp_int(x, y_prime), z);
      lemma_Exp_add(x, 2*y_prime, 1);
      lemma_ModMul(Exp_int(x, 2*y_prime), x, z);
      
      var mod_sx := ModExpPow2(sx, "1", 0, sz);
      var product := Mul(mod_sq_term, mod_sx);
      var final_res := ModExpPow2(product, "1", 0, sz);
      return final_res;
    }
  }
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
  /* code modified by LLM (iteration 10): calling recursive helper */
  res := ModExpRecursive(sx, sy, sz);
}
// </vc-code>
