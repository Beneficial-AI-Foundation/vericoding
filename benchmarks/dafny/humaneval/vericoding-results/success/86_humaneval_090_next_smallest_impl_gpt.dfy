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
  } else {
    var i := 1;
    var idx := 0;
    var m := s[0];
    while i < |s|
      invariant 1 <= i <= |s|
      invariant 0 <= idx < i
      invariant m == s[idx]
      invariant forall j :: 0 <= j < i ==> s[j] <= m
      decreases |s| - i
    {
      if s[i] > m {
        m := s[i];
        idx := i;
      }
      i := i + 1;
    }
    res := Some(m);
  }
}
// </vc-code>
