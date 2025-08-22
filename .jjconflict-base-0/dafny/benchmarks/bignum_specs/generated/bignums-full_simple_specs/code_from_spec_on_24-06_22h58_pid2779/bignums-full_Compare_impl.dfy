//IMPL Compare

/* code modified by LLM (iteration 3): Added missing helper functions */
predicate ValidBitString(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

/* code modified by LLM (iteration 3): Added function to convert bit string to integer */
function Str2Int(s: string): int
  requires ValidBitString(s)
{
  if |s| == 0 then 0
  else if s[0] == '0' then Str2Int(s[1..])
  else Power2(|s| - 1) + Str2Int(s[1..])
}

/* code modified by LLM (iteration 3): Added helper function for power of 2 */
function Power2(n: int): int
  requires n >= 0
{
  if n == 0 then 1
  else 2 * Power2(n - 1)
}

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  /* code modified by LLM (iteration 3): Convert to integers and compare directly */
  var val1 := Str2Int(s1);
  var val2 := Str2Int(s2);
  
  if val1 < val2 {
    res := -1;
  } else if val1 > val2 {
    res := 1;
  } else {
    res := 0;
  }
}