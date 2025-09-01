datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result : Option<string>)
  // post-conditions-start
  ensures result == None <==> |strings| == 0
  ensures result != None ==> forall s :: s in strings ==> |getVal(result)| >= |s|
  ensures result != None ==> getVal(result) in strings 
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |strings| == 0 {
    return None;
  } else {
    var maxLen := |strings[0]|;
    var longest := strings[0];
    var i := 1;
    while i < |strings|
      invariant 0 <= i <= |strings|
      invariant maxLen == |longest|
      invariant forall k :: 0 <= k < i ==> |strings[k]| <= maxLen
      invariant longest in strings[..i]
    {
      var len := |strings[i]|;
      if len > maxLen {
        maxLen := len;
        longest := strings[i];
      }
      i := i + 1;
    }
    return Some(longest);
  }
}
// </vc-code>

