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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
function Int2Str(n: nat): (s: string)
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else Int2Str(n/2) + (if n % 2 == 1 then "1" else "0")
}

/* helper modified by LLM (iteration 2): [fix char/string type errors] */
lemma Int2StrProperties(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n <= 1 {
    // Base cases are provable by unfolding
  } else {
    Int2StrProperties(n/2);
    var s_prefix := Int2Str(n/2);
    var last_char := if n % 2 == 1 then "1" else "0";
    assert Str2Int(s_prefix + last_char) == 2 * Str2Int(s_prefix) + (if last_char == "1" then 1 else 0);
  }
}

/* helper added by LLM (iteration 5): [helper lemma to unfold Str2Int] */
lemma Lemma_Str2Int_unfold(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

/* helper modified by LLM (iteration 3): [add non-ghost string to integer conversion method] */
/* helper modified by LLM (iteration 5): [fix loop invariant proof] */
method ComputeStr2Int(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[..i])
    decreases |s| - i
  {
    Lemma_Str2Int_unfold(s[..i+1]);
    n := 2 * n + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
}

/* helper added by LLM (iteration 5): [add lemma for power distribution over addition] */
lemma {:induction y2} Exp_int_distributes_over_add(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
  decreases y2
{
  if y2 > 0 {
    Exp_int_distributes_over_add(x, y1, y2 - 1);
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
  /* code modified by LLM (iteration 5): [add lemmas to fix timeout] */
  var x := ComputeStr2Int(sx);
  var z := ComputeStr2Int(sz);

  if |sy| == 1 {
    if sy[0] == '0' { 
      Int2StrProperties(1);
      res := Int2Str(1);
    } else { 
      var r_val := x % z;
      Int2StrProperties(r_val);
      res := Int2Str(r_val);
    }
  } else {
    var sy_prefix := sy[0..|sy|-1];
    var y_prefix_int := Str2Int(sy_prefix);
    
    Lemma_Str2Int_unfold(sy);
    Exp_int_distributes_over_add(x, y_prefix_int, y_prefix_int);
    
    var s_partial := ModExp(sx, sy_prefix, sz);
    var partial_val := ComputeStr2Int(s_partial);
    
    var val_sq := (partial_val * partial_val) % z;

    if sy[|sy|-1] == '0' {
      Int2StrProperties(val_sq);
      res := Int2Str(val_sq);
    } else {
      Exp_int_distributes_over_add(x, 2 * y_prefix_int, 1);
      var final_val := (val_sq * x) % z;
      Int2StrProperties(final_val);
      res := Int2Str(final_val);
    }
  }
}
// </vc-code>
