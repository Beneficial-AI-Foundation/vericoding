// <vc-preamble>
datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result : Option<string>)

  ensures result == None <==> |strings| == 0
  ensures result != None ==> forall s :: s in strings ==> |getVal(result)| >= |s|
  ensures result != None ==> getVal(result) in strings
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed implementation with loop invariants to ensure Dafny can verify postconditions */
{
  if |strings| == 0 {
    result := None;
  } else {
    var maxLen := |strings[0]|;
    var maxStr := strings[0];
    var i := 1;
    while i < |strings|
      invariant 1 <= i <= |strings|
      invariant maxLen == |maxStr|
      invariant forall j :: 0 <= j < i ==> |strings[j]| <= maxLen
      invariant maxStr in strings[0..i]
    {
      if |strings[i]| > maxLen {
        maxLen := |strings[i]|;
        maxStr := strings[i];
      }
      i := i + 1;
    }
    result := Some(maxStr);
  }
}
// </vc-code>
