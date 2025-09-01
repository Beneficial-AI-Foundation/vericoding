datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
const SECOND_MIN_DUMMY := 1000000000
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
    var min := s[0];
    var secondMin := SECOND_MIN_DUMMY;
    var countMin := 1;
    for i := 1 to |s| - 1 {
      if s[i] == min {
        countMin := countMin + 1;
      } else if s[i] < min {
        secondMin := min;
        min := s[i];
        countMin := 1;
      } else if s[i] > min && s[i] < secondMin {
        secondMin := s[i];
      }
    }
    if countMin == 1 && secondMin != SECOND_MIN_DUMMY {
      return Some(secondMin);
    } else {
      return None;
    }
  }
}
// </vc-code>

