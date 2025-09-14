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
  
  var longestStr := strings[0];
  var i := 1;
  
  while i < |strings|
    invariant 1 <= i <= |strings|
    invariant longestStr in strings
    invariant forall j :: 0 <= j < i ==> |longestStr| >= |strings[j]|
  {
    if |strings[i]| > |longestStr| {
      longestStr := strings[i];
    }
    i := i + 1;
  }
  
  return Some(longestStr);
}
// </vc-code>

