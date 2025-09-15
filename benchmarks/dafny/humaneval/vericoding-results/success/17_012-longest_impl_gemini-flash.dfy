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
{
  if |strings| == 0 {
    return None;
  } else {
    var longestString: string := strings[0];
    var i: int := 1;
    while i < |strings|
      invariant 0 <= i <= |strings|
      invariant forall j :: 0 <= j < i ==> |longestString| >= |strings[j]|
      invariant longestString in strings[..i]
    {
      if |strings[i]| > |longestString| {
        longestString := strings[i];
      }
      i := i + 1;
    }
    return Some(longestString);
  }
}
// </vc-code>
