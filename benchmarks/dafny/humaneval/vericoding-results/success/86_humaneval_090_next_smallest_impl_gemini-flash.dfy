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
predicate IsMax(val: int, s: seq<int>, k: int)
  requires 0 <= k < |s|
{
  (exists i :: 0 <= i <= k && s[i] == val) &&
  (forall i :: 0 <= i <= k ==> s[i] <= val)
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
    } else {
        var currentMax := s[0];
        var i := 1;
        while i < |s|
            invariant 1 <= i <= |s|
            invariant exists j :: 0 <= j < i && s[j] == currentMax
            invariant forall j :: 0 <= j < i ==> s[j] <= currentMax
        {
            if s[i] > currentMax {
                currentMax := s[i];
            }
            i := i + 1;
        }
        res := Some(currentMax);
    }
}
// </vc-code>
