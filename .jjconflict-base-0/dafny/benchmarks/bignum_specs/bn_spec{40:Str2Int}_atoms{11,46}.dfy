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

// SPEC BN_40 (modified version wrt Google Sheets)
function Str2Int(s: string): nat 
requires ValidBitString(s)
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{}

