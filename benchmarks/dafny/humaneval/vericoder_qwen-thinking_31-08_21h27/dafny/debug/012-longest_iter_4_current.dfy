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
if strings.Length == 0 {
    return None;
}
var result := Some(strings[0]);
var i := 1;
while i < strings.Length
    invariant i <= strings.Length
    invariant result != None
    invariant forall j :: 0 <= j < i ==> strings[j].Length <= getVal(result).Length
    invariant getVal(result) in strings[0..i-1]
{
    if strings[i].Length > getVal(result).Length {
        result := Some(strings[i]);
    }
    i := i + 1;
}
return result;
// </vc-code>

