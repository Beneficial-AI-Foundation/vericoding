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
function max(a: int, b: int): int {
  if a >= b then a else b
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
  /* code modified by LLM (iteration 4): added loop invariants to ensure mx is the maximum value and mi holds an index of a maximum element for verification */
  if |s| < 2 {
    return None;
  } else {
    var mx := s[0];
    var mi := 0;
    var i := 1;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==> s[k] <= mx
      invariant 0 <= mi < i
      invariant s[mi] == mx
    {
      if s[i] > mx {
        mx := s[i];
        mi := i;
      }
      i := i + 1;
    }
    return Some(mx);
  }
}
// </vc-code>
