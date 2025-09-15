// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed loop invariants and added proper triggers */
  if |sub| == 0 {
    result := true;
    return;
  }
  if |sub| > |s| {
    result := false;
    return;
  }
  
  var i := 0;
  result := false;
  while i <= |s| - |sub|
    invariant 0 <= i <= |s| - |sub| + 1
    invariant result ==> exists k {:trigger s[k..k+|sub|]} :: 0 <= k < i && s[k..k+|sub|] == sub
  {
    var isMatch := true;
    var j := 0;
    while j < |sub|
      invariant 0 <= j <= |sub|
      invariant isMatch ==> (j == 0 || s[i..i+j] == sub[0..j])
      invariant !isMatch ==> exists jj :: 0 <= jj < j && s[i+jj] != sub[jj]
    {
      if s[i+j] != sub[j] {
        isMatch := false;
        break;
      }
      j := j + 1;
    }
    if isMatch {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
