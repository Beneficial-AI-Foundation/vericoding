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
/* helper modified by LLM (iteration 5): added parentheses to fix parse error */
function findLongest(s: seq<string>): string
    requires |s| > 0
    ensures result in s
    ensures forall x :: x in s ==> |result| >= |x|
    decreases |s|
{
    if |s| > 1 then
        (let tail_longest := findLongest(s[1..]) in
            if |s[0]| >= |tail_longest| then s[0] else tail_longest)
    else
        s[0]
}
// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result : Option<string>)

  ensures result == None <==> |strings| == 0
  ensures result != None ==> forall s :: s in strings ==> |getVal(result)| >= |s|
  ensures result != None ==> getVal(result) in strings
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): No change; bug was in the helper function. */
  if |strings| == 0 {
    result := None;
  } else {
    result := Some(findLongest(strings));
  }
}
// </vc-code>
