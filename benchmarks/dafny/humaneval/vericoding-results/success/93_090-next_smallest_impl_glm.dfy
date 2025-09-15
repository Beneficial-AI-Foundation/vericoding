// <vc-preamble>
datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed redundant helper and fixed AllLeq predicate */
predicate AllLeq(val: int, s: seq<int>) {
  forall i :: 0 <= i < |s| ==> s[i] <= val
}

// </vc-helpers>

// <vc-spec>
method rolling_max(s: seq<int>) returns (res: Option<int>) 

    ensures res == None <==> |s| < 2
    ensures res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= getVal(res) || s[y] <= getVal(res)
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 4): fixed loop invariant to prevent index out of range error */
  if |s| < 2 {
    res := None;
  } else {
    var maxIndex := 0;
    var i := 1;
    while i < |s|
      invariant 0 <= maxIndex < |s|
      invariant 1 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> s[j] <= s[maxIndex]
    {
      if s[i] > s[maxIndex] {
        maxIndex := i;
      }
      i := i + 1;
    }
    res := Some(s[maxIndex]);
  }
}
// </vc-code>
