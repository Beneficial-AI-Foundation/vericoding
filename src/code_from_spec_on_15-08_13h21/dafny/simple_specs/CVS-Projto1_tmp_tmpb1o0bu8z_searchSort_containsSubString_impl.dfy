//IMPL containsSubString
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
    /* code modified by LLM (iteration 2): renamed 'match' to 'found' since 'match' is a reserved keyword in Dafny */
    var found := true;
    
    while j < b.Length && found
    {
      /* code modified by LLM (iteration 2): removed 'then' keyword when using braces */
      if a[i + j] != b[j] {
        found := false;
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 2): updated variable name from 'match' to 'found' */
    if found {
      pos := i;
      return;
    }
    
    i := i + 1;
  }
  
  pos := -1;
}