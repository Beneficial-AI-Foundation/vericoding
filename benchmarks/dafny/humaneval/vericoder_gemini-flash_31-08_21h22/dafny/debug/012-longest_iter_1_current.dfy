datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function method in_seq<T>(elem: T, s: seq<T>): bool {
  exists i :: 0 <= i < |s| && s[i] == elem
}
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
  }

  var maxLength := -1;
  var longestString: Option<string> := None;

  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant longestString == None || (longestString != None && getVal(longestString) in_seq strings && forall k :: 0 <= k < i && k < |strings| ==> |getVal(longestString)| >= |strings[k]|)
    invariant longestString == None ==> maxLength == -1
    invariant longestString != None ==> maxLength == |getVal(longestString)|
  {
    var currentString := strings[i];
    if |currentString| > maxLength {
      maxLength := |currentString>;
      longestString := Some(currentString);
    }
    i := i + 1;
  }
  return longestString;
}
// </vc-code>

