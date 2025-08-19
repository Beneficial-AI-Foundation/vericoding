//IMPL 
method AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{
  if |s| <= 1 {
    result := true;
  } else {
    var i := 1;
    result := true;
    /* code modified by LLM (iteration 1): enhanced loop invariant to track witness indices for postcondition */
    while i < |s| && result
      invariant 1 <= i <= |s|
      invariant result ==> forall k :: 0 <= k < i ==> s[k] == s[0]
      invariant !result ==> exists k :: 1 <= k < i && s[k] != s[0]
    {
      if s[i] != s[0] {
        result := false;
      }
      i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to help prove postcondition when result is false */
    if !result {
      assert exists k :: 1 <= k < i && s[k] != s[0];
      assert exists k :: 0 <= k < |s| && 0 <= 0 < |s| && k != 0 && s[k] != s[0];
    }
  }
}