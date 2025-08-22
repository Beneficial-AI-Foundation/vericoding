// ATOM BN_11
predicate ValidBitString(s: string) 
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM BN_46
function Exp_int(x: nat, y:nat): nat 
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

// IMPL BN_40
function Str2Int(s: string): nat 
requires ValidBitString(s)
/* code modified by LLM (iteration 1): Fixed malformed ensures clause - removed undefined variable i and corrected the recursive property */
ensures |s| > 0 ==> Str2Int(s) == (if s[0] == '1' then 1 else 0) * Exp_int(2, |s|-1) + Str2Int(s[1..])
ensures |s| == 0 ==> Str2Int(s) == 0
{
  if |s| == 0 then 
    0
  else 
    (if s[0] == '1' then 1 else 0) * Exp_int(2, |s|-1) + Str2Int(s[1..])
}