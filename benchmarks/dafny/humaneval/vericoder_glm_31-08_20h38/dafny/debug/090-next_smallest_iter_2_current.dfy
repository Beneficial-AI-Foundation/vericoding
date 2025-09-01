datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>

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
      return None;
  }
  var max := s[0];
  var i := 1;
  while i < |s|
      invariant 1 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> s[j] <= max
      invariant max in s[..i]
  {
      if s[i] > max {
          max := s[i];
      }
      i := i + 1;
  }
  return Some(max);
}
// </vc-code>

