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
/* helper modified by LLM (iteration 7): provided proof to prevent timeout */
lemma LemmaModOfSumWithMultiple(x: nat, y: nat, n: nat)
    requires n > 0
    requires x % n == 0
    ensures (x + y) % n == y % n
{
    var qx := x / n;
    assert x == qx * n;

    var ry := y % n;
    var qy := y / n;
    assert y == qy * n + ry;
    
    assert x + y == (qx + qy) * n + ry;
    assert (x + y) % n == ry;
}

/* helper modified by LLM (iteration 7): expanded proof to prevent timeout */
lemma LemmaModMult(a: nat, b: nat, n: nat)
    requires n > 0
    ensures (a * b) % n == ((a % n) * (b % n)) % n
{
    var ra := a % n;
    var rb := b % n;
    var qa := a / n;
    var qb := b / n;
    assert a == qa * n + ra;
    assert b == qb * n + rb;
    
    var remainder_part := ra * rb;
    var multiple_part_inner := qa * qb * n + qa * rb + ra * qb;
    var multiple_part := n * multiple_part_inner;

    calc {
        a * b;
        == (qa * n + ra) * (qb * n + rb);
        == qa * n * (qb * n + rb) + ra * (qb * n + rb);
        == qa * n * qb * n + qa * n * rb + ra * qb * n + ra * rb;
        == n * (qa * qb * n + qa * rb + ra * qb) + ra * rb;
        == multiple_part + remainder_part;
    }
    
    assert multiple_part % n == 0;

    LemmaModOfSumWithMultiple(multiple_part, remainder_part, n);
    
    calc {
        (a * b) % n;
        == { assert a * b == multiple_part + remainder_part; }
           (multiple_part + remainder_part) % n;
        == { LemmaModOfSumWithMultiple(multiple_part, remainder_part, n); }
           remainder_part % n;
        == { assert remainder_part == (a % n) * (b % n); }
           ((a % n) * (b % n)) % n;
    }
}

/* helper modified by LLM (iteration 4): expanded proof of LemmaModMultOneArg to fix timeout */
lemma LemmaModMultOneArg(a: nat, b: nat, n: nat)
    requires n > 0
    ensures (a * (b % n)) % n == (a * b) % n
{
    LemmaModMult(a, b, n);
    var rb := b % n;
    assert 0 <= rb < n ==> rb % n == rb;
    LemmaModMult(a, rb, n);
    
    calc {
        (a * (b % n)) % n;
        == (a * rb) % n;
        == { LemmaModMult(a, rb, n); }
        ((a % n) * (rb % n)) % n;
        == { assert rb % n == rb; }
        ((a % n) * rb) % n;
        == ((a % n) * (b % n)) % n;
        == { LemmaModMult(a, b, n); }
        (a * b) % n;
    }
}

lemma LemmaExpPlus(base: nat, exp1: nat, exp2: nat)
    ensures Exp_int(base, exp1 + exp2) == Exp_int(base, exp1) * Exp_int(base, exp2)
    decreases exp2
{
    if exp2 > 0 {
        calc {
            Exp_int(base, exp1 + exp2);
            == base * Exp_int(base, exp1 + exp2 - 1);
            == base * Exp_int(base, exp1 + (exp2 - 1));
            == { LemmaExpPlus(base, exp1, exp2 - 1); }
            base * (Exp_int(base, exp1) * Exp_int(base, exp2 - 1));
            ==
            Exp_int(base, exp1) * (base * Exp_int(base, exp2 - 1));
            == Exp_int(base, exp1) * Exp_int(base, exp2);
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
  /* code modified by LLM (iteration 7): no changes to logic, fixed helper timeouts */
  if |sy| == 1 {
    if sy[0] == '0' {
       // Exp_int(x, 0) % z == 1 % z == 1 (since z > 1)
       res := "1";
    } else { // sy[0] == '1'
       // Exp_int(x, 1) % z == x % z 
       var _, rem := DivMod(sx, sz);
       res := rem;
    }
  } else {
    var y_half_s := sy[..|sy|-1];
    var last_bit := sy[|sy|-1];

    var temp_res_s := ModExp(sx, y_half_s, sz);
    
    var temp_res_sq_s := Mul(temp_res_s, temp_res_s);

    var _, res_even_s := DivMod(temp_res_sq_s, sz);
    
    ghost var x := Str2Int(sx);
    ghost var y_half := Str2Int(y_half_s);
    ghost var z := Str2Int(sz);
    ghost var y := Str2Int(sy);
    
    // Prove properties of res_even_s for both branches
    assert Str2Int(res_even_s) == (Exp_int(x, y_half) % z * Exp_int(x, y_half) % z) % z;
    LemmaModMult(Exp_int(x, y_half), Exp_int(x, y_half), z);
    assert Str2Int(res_even_s) == (Exp_int(x, y_half) * Exp_int(x, y_half)) % z;
    LemmaExpPlus(x, y_half, y_half);
    assert Str2Int(res_even_s) == Exp_int(x, 2 * y_half) % z;

    if last_bit == '0' {
      assert y == 2 * y_half;
      res := res_even_s;
    } else { // last_bit == '1'
      assert y == 2 * y_half + 1;
      var temp_prod_s := Mul(sx, res_even_s);
      
      var _, rem_odd_s := DivMod(temp_prod_s, sz);

      LemmaModMultOneArg(x, Exp_int(x, 2 * y_half), z);
      LemmaExpPlus(x, 1, 2 * y_half);

      res := rem_odd_s;
    }
  }
}
// </vc-code>
