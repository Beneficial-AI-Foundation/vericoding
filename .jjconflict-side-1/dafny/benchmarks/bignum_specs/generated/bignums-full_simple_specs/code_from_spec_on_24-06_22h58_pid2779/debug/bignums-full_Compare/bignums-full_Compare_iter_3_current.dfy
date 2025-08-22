//IMPL Compare

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  /* code modified by LLM (iteration 2): Convert to integers and compare directly */
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