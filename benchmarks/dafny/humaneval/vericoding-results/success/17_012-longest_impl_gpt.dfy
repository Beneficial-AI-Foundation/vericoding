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
/* helper modified by LLM (iteration 2): replaced generic predicate causing equality trait error with a simple utility function */
function selectLonger(a: string, b: string): string { if |a| >= |b| then a else b }
// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result : Option<string>)

  ensures result == None <==> |strings| == 0
  ensures result != None ==> forall s :: s in strings ==> |getVal(result)| >= |s|
  ensures result != None ==> getVal(result) in strings
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented iterative scan to find longest string with proper invariants */
  if |strings| == 0 {
    result := None;
  } else {
    var best := strings[0];
    var i := 1;
    while i < |strings|
      invariant 1 <= i && i <= |strings|
      invariant exists k:int :: 0 <= k && k < i && strings[k] == best
      invariant forall j:int :: 0 <= j && j < i ==> |best| >= |strings[j]|
      decreases |strings| - i
    {
      if |strings[i]| > |best| {
        best := strings[i];
      }
      i := i + 1;
    }
    result := Some(best);
  }
}
// </vc-code>
