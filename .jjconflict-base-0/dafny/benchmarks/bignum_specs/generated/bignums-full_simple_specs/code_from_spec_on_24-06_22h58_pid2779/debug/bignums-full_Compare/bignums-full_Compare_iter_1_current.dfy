The key insight is that I can use the existing `NormalizeBitString` method to remove leading zeros, then compare the normalized strings efficiently:


//IMPL Compare

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  var norm1 := NormalizeBitString(s1);
  var norm2 := NormalizeBitString(s2);
  
  if |norm1| < |norm2| {
    res := -1;
  } else if |norm1| > |norm2| {
    res := CompareUnequal(norm1, norm2);
  } else {
    // Same length, compare lexicographically
    if norm1 < norm2 {
      res := -1;
    } else if norm1 > norm2 {
      res := 1;
    } else {
      res := 0;
    }
  }
}