datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method rolling_max(s: seq<int>) returns (res: Option<int>) 
    // post-conditions-start
    ensures res == None <==> |s| < 2
    ensures res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= getVal(res) || s[y] <= getVal(res)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| < 2 {
    res := None;
  } else {
    var mx := s[0];
    var w := 0;
    var i := 1;
    while i < |s|
      invariant 1 <= i <= |s|
      invariant 0 <= w < i
      invariant mx == s[w]
      invariant forall k :: 0 <= k < i ==> s[k] <= mx
      invariant exists x :: 0 <= x < i && s[x] == mx
      decreases |s| - i
    {
      if s[i] > mx {
        mx := s[i];
        w := i;
      }
      i := i + 1;
    }
    assert exists x :: 0 <= x < |s| && s[x] == mx;
    res := Some(mx);
  }
}
// </vc-code>

