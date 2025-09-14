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

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
function subtractBits(b1: char, b2: char, borrow: int) : (char, int)
  requires (b1 == '0' || b1 == '1') && (b2 == '0' || b2 == '1') && (borrow == 0 || borrow == 1)
  ensures var diff := (if b1 == '1' then 1 else 0) - (if b2 == '1' then 1 else 0) - borrow;
          var newBorrow := if diff < 0 then 1 else 0;
          var resultBit := if (diff % 2 == 0) then '0' else '1';
          (resultBit, newBorrow) == (if diff == -2 then ('0', 1) else if diff == -1 then ('1', 1) else if diff == 0 then ('0', 0) else if diff == 1 then ('1', 0) else ('error', 2)) // 'error' case for exhaustive definition
  ensures (var rBit, rBorrow := subtractBits(b1, b2, borrow);
    (if b1 == '1' then 1 else 0) - (if b2 == '1' then 1 else 0) - borrow
    == (if rBit == '1' then 1 else 0) - (rBorrow * 2))
{
  var v1 := if b1 == '1' then 1 else 0;
  var v2 := if b2 == '1' then 1 else 0;
  var diff := v1 - v2 - borrow;
  if diff == -2 then ('0', 1)
  else if diff == -1 then ('1', 1)
  else if diff == 0 then ('0', 0)
  else if diff == 1 then ('1', 0)
  else ('0', 0) // Should not be reached given preconditions
}

function PaddedString(s: string, len: nat) : string
  ensures |PaddedString(s, len)| == len
  ensures ValidBitString(PaddedString(s, len))
  ensures ValidBitString(s) ==> Str2Int(PaddedString(s, len)) == Str2Int(s)
{
  if |s| < len then PaddedString("0" + s, len)
  else s
}

ghost function Pow2(power: nat): nat
{
  if power == 0 then 1 else 2 * Pow2(power - 1)
}

// Added helper function to construct string slice for Str2Int in invariant
ghost function GetStringSlice(arr: array<char>, start: nat, end: nat): string
  requires start <= end <= arr.Length
  requires forall i :: 0 <= i < arr.Length ==> arr[i] == '0' || arr[i] == '1'
  ensures var s := GetStringSlice(arr, start, end);
          |s| == end - start
  ensures forall k | 0 <= k < |s| :: s[k] == arr[start + k]
{
  var s := "";
  for k := start to end - 1 {
    s := s + arr[k];
  }
  return s;
}
// </vc-helpers>

// <vc-spec>
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var len := |s1|;
  if |s2| > len { len := |s2|; }

  var p_s1 := PaddedString(s1, len);
  var p_s2 := PaddedString(s2, len);

  var result_bits := new char[len];
  var borrow := 0;
  var i := len - 1;

  while i >= 0
    invariant -1 <= i < len
    invariant ValidBitString(p_s1) && ValidBitString(p_s2)
    invariant forall k | i < k < len :: (result_bits[k] == '0' || result_bits[k] == '1')
    invariant borrow == 0 || borrow == 1
    // Corrected invariant to use GetStringSlice for Str2Int on result_bits
    invariant (Str2Int(p_s1[i+1 .. len]) - Str2Int(p_s2[i+1 .. len]) - (borrow as int)) == (if i < len - 1 then Str2Int(GetStringSlice(result_bits, i+1, len)) else 0)
    invariant (Str2Int(p_s1) - Str2Int(p_s2)) == (Str2Int(GetStringSlice(result_bits, i + 1, len)) * Pow2((len - (i + 1)) as nat)) + (Str2Int(p_s1[0..i+1]) - Str2Int(p_s2[0..i+1]) - borrow)
    invariant forall k :: 0 <= k < len ==> (result_bits[k] == '0' || result_bits[k] == '1') || k > i // All initialized parts are valid bits
    decreases i
  {
    var b1 := p_s1[i];
    var b2 := p_s2[i];
    var (rBit, newBorrow) := subtractBits(b1, b2, borrow);
    result_bits[i] := rBit;
    borrow := newBorrow;
    i := i - 1;
  }

  assert borrow == 0;

  var temp_res_string := new string(result_bits);


  var first_one_idx := 0;
  while first_one_idx < |temp_res_string| - 1 && temp_res_string[first_one_idx] == '0'
    invariant 0 <= first_one_idx <= |temp_res_string| - 1
    invariant temp_res_string != ""
  {
    first_one_idx := first_one_idx + 1;
  }

  res := temp_res_string[first_one_idx..];

  if res == "" then res := "0";
  else if Str2Int(res) == 0 then res := "0";

  if Str2Int(s1) == Str2Int(s2) then res := "0";
}
// </vc-code>

