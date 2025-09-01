datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
// No helpers required for verification.
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
    return;
  }
  var n := |s|;
  var idx := 0;
  var i := 1;
  while i < n
    invariant 0 <= idx < n
    invariant 1 <= i <= n
    invariant forall j :: 0 <= j < i ==> s[j] <= s[idx]
    decreases n - i
  {
    if s[i] > s[idx] {
      idx := i;
    }
    i := i + 1;
  }
  res := Some(s[idx]);
}
// </vc-code>

