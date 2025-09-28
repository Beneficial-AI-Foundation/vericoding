// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed from 'function method' to 'method' to fix parse error */
method Str2Nat(s: string) returns (res: nat)
  requires ValidBitString(s)
  ensures res == Str2Int(s)
{
  res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res == Str2Int(s[..i])
  {
    var bit := if s[i] == '1' then 1 else 0;
    res := 2 * res + bit;
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 4): changed 'var' to 'let' to fix parse error in function */
function Int2Str(n: nat): (s: string)
  ensures ValidBitString(s)
  ensures (n == 0) <==> (s == "0")
  ensures n > 0 ==> s[0] == '1'
  decreases n
{
  if n == 0 then "0"
  else
    let rest := Int2Str(n/2) in
    let last_bit := if n % 2 == 1 then "1" else "0" in
      if rest == "0" then last_bit
      else rest + last_bit
}

/* helper modified by LLM (iteration 4): no changes, lemma is correct and needed */
lemma Lemma_Str2Int_of_Int2Str(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n > 0 {
    Lemma_Str2Int_of_Int2Str(n/2);
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
/* code modified by LLM (iteration 4): logic is correct, calls fixed helpers */
{
  var D_int := Str2Nat(dividend);
  var d_int := Str2Nat(divisor);

  var q_int := D_int / d_int;
  var r_int := D_int % d_int;

  Lemma_Str2Int_of_Int2Str(q_int);
  quotient := Int2Str(q_int);
  
  Lemma_Str2Int_of_Int2Str(r_int);
  remainder := Int2Str(r_int);
}
// </vc-code>
