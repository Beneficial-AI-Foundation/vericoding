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
    result := None;
    return;
  }
  var best := strings[0];
  var i := 1;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant exists j :: 0 <= j < i && strings[j] == best
    invariant forall j :: 0 <= j < i ==> |best| >= |strings[j]|
  {
    if |strings[i]| > |best| {
      best := strings[i];
    }
    i := i + 1;
  }
  result := Some(best);
  return;
}
// </vc-code>

