//IMPL 

method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
  requires 0 <= b.Length <= a.Length
{
  if b.Length == 0 {
    pos := 0;
    return;
  }
  
  var i := 0;
  while i <= a.Length - b.Length
  {
    var j := 0;
    var found := true;
    
    while j < b.Length && found
    {
      if a[i + j] != b[j] {
        found := false;
      }
      j := j + 1;
    }
    
    if found {
      pos := i;
      return;
    }
    
    i := i + 1;
  }
  
  pos := -1;
}