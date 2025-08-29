datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma max_of_two(a: int, b: int)
  ensures a >= b || b >= a
{
}
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
  
  var max_val := s[0];
  for i := 1 to |s|
    invariant 0 < i <= |s|
    invariant exists x :: 0 <= x < i && s[x] == max_val
    invariant forall x :: 0 <= x < i ==> s[x] <= max_val
  {
    if s[i] > max_val {
      max_val := s[i];
    }
  }
  return Some(max_val);
}
// </vc-code>
