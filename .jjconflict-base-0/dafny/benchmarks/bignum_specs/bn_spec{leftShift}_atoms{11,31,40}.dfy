// ATOM BN_11
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM BN_31
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// ATOM BN_40
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// SPEC leftShift
method leftShift(s: string, n: nat) returns (res: string)
    requires ValidBitString(s)
    ensures ValidBitString(res)
    ensures Str2Int(res) == Str2Int(s) * Pow2(n)
{}
