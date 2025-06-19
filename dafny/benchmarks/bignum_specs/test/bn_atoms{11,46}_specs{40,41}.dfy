// ATOM
predicate ValidBitString(s: string) // BN_11
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM
function Exp_int(x: nat, y:nat): nat // BN_46
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}


// SPEC
// BN_40 - HAS TO BE AN ATOM ? 
function Str2Int(s: string): nat 
  requires ValidBitString(s)
{}

// SPEC 
// BN_41
lemma Str2IntLemma(s: string, i: nat)
requires ValidBitString(s)
requires 0 <= i <= |s|-1
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{}
