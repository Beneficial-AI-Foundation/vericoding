//ATOM
// method verifies
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0
requires |s| > 0 ==> i < |s| && j < |s|
ensures multiset(s[..]) == multiset(t[..])
ensures |s| == |t|
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i]
ensures |s| == 0 ==> t == s
{
  if |s| == 0 {
    t := s;
  } else {
    /* code modified by LLM (iteration 1): fixed sequence slicing bounds and proper swapping logic to handle all cases */
    if i == j {
      t := s;
    } else {
      var minIdx := if i < j then i else j;
      var maxIdx := if i < j then j else i;
      var charAtI := s[i];
      var charAtJ := s[j];
      
      t := s[..minIdx] + [if minIdx == i then charAtJ else charAtI] + 
           s[minIdx+1..maxIdx] + [if maxIdx == i then charAtJ else charAtI] + 
           s[maxIdx+1..];
    }
  }
}

//IMPL SPEC
method check()
{
  /* code modified by LLM (iteration 1): added simple test case to demonstrate StringSwap usage */
  var result := StringSwap("ab", 0, 1);
  assert result == "ba";
}