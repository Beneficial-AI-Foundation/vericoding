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
  } else {
    var current := Some(strings[0]);
    var i := 1;
    while i < |strings|
      invariant 0 <= i <= |strings|
      invariant current != None && getVal(current) in strings[0..i]
      invariant forall j :: 0 <= j < i ==> |getVal(current)| >= |strings[j]|
    {
      if |strings[i]| > |getVal(current)| {
        current := Some(strings[i]);
      }
      i := i + 1;
    }
    return current;
  }
}
// </vc-code>

