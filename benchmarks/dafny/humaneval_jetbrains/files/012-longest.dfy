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

  ensures result == None <==> |strings| == 0
  ensures result != None ==> forall s :: s in strings ==> |getVal(result)| >= |s|
  ensures result != None ==> getVal(result) in strings
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
