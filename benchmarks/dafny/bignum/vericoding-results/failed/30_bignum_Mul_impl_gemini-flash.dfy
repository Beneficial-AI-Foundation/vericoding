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
function MultiplyBitStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(MultiplyBitStrings(s1, s2))
  ensures Str2Int(MultiplyBitStrings(s1, s2)) == Str2Int(s1) * Str2Int(s2)
{
  if s1 == "0" || s2 == "0" then
    "0"
  else if s1 == "1" then
    s2
  else if s2 == "1" then
    s1
  else
  {
    var num1 := Str2Int(s1);
    var num2 := Str2Int(s2);
    var product := num1 * num2;
    var resultStr := Int2Str(product);
    resultStr
  }
}

ghost function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then
    "0"
  else
  {
    var s := "";
    var temp_n := n;
    var k := 0; // Tracks the current bit position (power of 2)
    while temp_n > 0
      invariant temp_n >= 0
      invariant n == Str2Int(s) * (1 << k) + temp_n
      decreases temp_n
    {
      if temp_n % 2 == 1 then
        s := "1" + s
      else
        s := "0" + s;
      temp_n := temp_n / 2;
      k := k + 1; // Increment the bit position
    }
    s
  }
}

ghost function BitLength(n: nat): nat
  decreases n
{
  if n == 0 then 0 else 1 + BitLength(n / 2)
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
  res := MultiplyBitStrings(s1, s2);
}
// </vc-code>

