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
function max(a: int, b: int): int { if a > b then a else b }
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
    var current_max := max(s[0], s[1]);
    var i := 2;
    while i < |s|
      invariant 2 <= i <= |s|
      invariant exists k :: 0 <= k < i && current_max == s[k]
      invariant forall j :: 0 <= j < i ==> s[j] <= current_max
    {
      current_max := max(current_max, s[i]);
      i := i + 1;
    }
    res := Some(current_max);
  }
}
// </vc-code>
