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
lemma RollingMaxLemma(s: seq<int>, i: int) 
  requires 0 <= i < |s|
  ensures forall x :: 0 <= x <= i ==> s[x] <= seq_max(s[..i+1])
  ensures exists x :: 0 <= x <= i && s[x] == seq_max(s[..i+1])
{
  if i == 0 {
  } else {
    RollingMaxLemma(s, i-1);
  }
}
function seq_max(s: seq<int>): int 
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] <= seq_max(s)
  ensures exists i :: 0 <= i < |s| && s[i] == seq_max(s)
{
  if |s| == 1 then
    s[0]
  else
    max(s[0], seq_max(s[1..]))
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
    return;
  }
  
  var max_val := s[0];
  var max_idx := 0;
  var i := 1;
  
  while i < |s|
    invariant 1 <= i <= |s|
    invariant max_idx < i
    invariant s[max_idx] == max_val
    invariant forall x :: 0 <= x < i ==> s[x] <= max_val
  {
    if s[i] > max_val {
      max_val := s[i];
      max_idx := i;
    }
    i := i + 1;
  }
  
  RollingMaxLemma(s, |s|-1);
  res := Some(max_val);
}
// </vc-code>
