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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * pow2(n-1)
}

method AddHelper(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var carry := 0;
  var i := 0;
  var len := if |s1| > |s2| then |s1| else |s2|;
  res := "";
  
  while i < len || carry != 0
    decreases len - i + if carry != 0 then 1 else 0
    invariant ValidBitString(res)
    invariant Str2Int(res) + carry * (pow2(i)) == 
      Str2Int(s1[|s1|-i..]) + Str2Int(s2[|s2|-i..])
    invariant |res| == i
  {
    var digit1 := if i < |s1| then (if s1[|s1| - 1 - i] == '1' then 1 else 0) else 0;
    var digit2 := if i < |s2| then (if s2[|s2| - 1 - i] == '1' then 1 else 0) else 0;
    var sum := digit1 + digit2 + carry;
    carry := sum / 2;
    res := (if sum % 2 == 1 then "1" else "0") + res;
    i := i + 1;
  }
  
  if res == "" {
    res := "0";
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  res := "0";
  for i := 0 to |s2|
    invariant ValidBitString(res)
    invariant Str2Int(res) == Str2Int(s1) * Str2Int(s2[|s2|-i..])
  {
    if i < |s2| {
      var bit := s2[|s2|-1-i];
      if bit == '1' {
        var shifted := s1;
        var j := 0;
        while j < i
          invariant ValidBitString(shifted)
          invariant Str2Int(shifted) == Str2Int(s1) * pow2(j)
        {
          shifted := shifted + "0";
          j := j + 1;
        }
        res := AddHelper(res, shifted);
      }
    }
  }
  return res;
}
// </vc-code>

