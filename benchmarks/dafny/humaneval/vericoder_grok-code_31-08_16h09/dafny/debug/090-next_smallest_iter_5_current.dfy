datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
const SECOND_MAX_DUMMY : int := 1000000000;
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
  } else {
    var max := s[0];
    var secondMax : Option<int> := None;
    var hasSecond := false;
    for i := 1 to |s| - 1 {
      if s[i] > max {
        secondMax := if hasSecond then secondMax else Some(max);
        hasSecond := true;
        max := s[i];
      } else if s[i] == max {
        // do nothing
      } else { // s[i] < max
        if !hasSecond {
          secondMax := Some(s[i]);
          hasSecond := true;
        } else if s[i] > getVal(secondMax) {
          secondMax := Some(s[i]);
        }
      }
    }
    if hasSecond {
      return Some(getVal(secondMax));
    } else {
      return Some(max);
    }
  }
}
// </vc-code>

