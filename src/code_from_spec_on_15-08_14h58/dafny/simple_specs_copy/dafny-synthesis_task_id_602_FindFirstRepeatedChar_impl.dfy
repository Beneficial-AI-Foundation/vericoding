//IMPL 
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
  ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
  found := false;
  c := if |s| > 0 then s[0] else 'a'; // initialize c to avoid compilation issues
  
  /* code modified by LLM (iteration 1): added early return for empty string and fixed loop invariant */
  if |s| <= 1 {
    return;
  }
  
  var j := 1;
  while j < |s|
    invariant 1 <= j <= |s|
    invariant !found ==> (forall i1, j1 :: 0 <= i1 < j1 < j ==> s[i1] != s[j1])
  {
    var i := 0;
    while i < j
      invariant 0 <= i <= j
      invariant !found ==> (forall i1 :: 0 <= i1 < i ==> s[i1] != s[j])
    {
      if s[i] == s[j] {
        found := true;
        c := s[i];
        return;
      }
      i := i + 1;
    }
    j := j + 1;
  }
}