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
lemma getVal_Some(mx: Option<int>, v: int)
  requires mx == Some(v)
  ensures getVal(mx) == v
{
  match mx {
    case Some(n) => assert n == v;
  }
}
// </vc-helpers>

// <vc-spec>
method rolling_max(s: seq<int>) returns (res: Option<int>) 

    ensures res == None <==> |s| < 2
    ensures res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= getVal(res) || s[y] <= getVal(res)
// </vc-spec>
// <vc-code>
{
  if |s| < 2 {
    res := None;
    return;
  } else {
    var i := 1;
    var idx := 0;
    var curr := s[0];
    while i < |s|
      invariant 0 <= i <= |s|
      invariant 0 <= idx < |s|
      invariant curr == s[idx]
      invariant forall k :: 0 <= k < i ==> s[k] <= curr
    {
      if s[i] > curr {
        curr := s[i];
        idx := i;
      }
      i := i + 1;
    }
    res := Some(curr);
    return;
  }
}
// </vc-code>
