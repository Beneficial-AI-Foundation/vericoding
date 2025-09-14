ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
method AddWithCarry(s1: string, s2: string, carry: int) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2) && (carry == 0 || carry == 1)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2) + carry
  decreases |s1| + |s2|
{
  if |s1| == 0 && |s2| == 0 {
    if carry == 0 {
      return "";
    } else {
      return "1";
    }
  } else {
    var x := if |s1|>0 then (if s1[|s1|-1]=='1' then 1 else 0) else 0;
    var y := if |s2|>0 then (if s2[|s2|-1]=='1' then 1 else 0) else 0;
    var total := x + y + carry;
    var newCarry := total / 2;
    var bit := total % 2;
    var s1' := if |s1|>0 then s1[0..|s1|-1] else "";
    var s2' := if |s2|>0 then s2[0..|s2|-1] else "";
    var res' := AddWithCarry(s1', s2', newCarry);
    return res' + (if bit==1 then "1" else "0");
  }
}
// </vc-helpers>

// <vc-spec>
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var result := AddWithCarry(s1, s2, 0);
  return result;
}
// </vc-code>

