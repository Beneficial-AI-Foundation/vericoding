// <vc-preamble>
function filter(s: seq<int>, p: int -> bool): seq<int>
{
    if |s| == 0 then []
    else if p(s[0]) then [s[0]] + filter(s[1..], p)
    else filter(s[1..], p)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove filter property for loop invariant */
lemma FilterAppend(s: seq<int>, p: int -> bool, elem: int)
  ensures p(elem) ==> filter(s + [elem], p) == filter(s, p) + [elem]
  ensures !p(elem) ==> filter(s + [elem], p) == filter(s, p)
{
  if |s| == 0 {
    assert s + [elem] == [elem];
  } else {
    assert (s + [elem])[0] == s[0];
    assert (s + [elem])[1..] == s[1..] + [elem];
    FilterAppend(s[1..], p, elem);
  }
}
// </vc-helpers>

// <vc-spec>
method myfun4(x: seq<int>) returns (y: seq<int>)
    ensures y == filter(x, k => k % 3 == 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariant maintenance using helper lemma */
{
  y := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant y == filter(x[..i], k => k % 3 == 0)
  {
    var old_y := y;
    if x[i] % 3 == 0 {
      y := y + [x[i]];
    }
    assert x[..i+1] == x[..i] + [x[i]];
    FilterAppend(x[..i], k => k % 3 == 0, x[i]);
    i := i + 1;
  }
  assert x[..|x|] == x;
}
// </vc-code>
