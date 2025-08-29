// <vc-helpers>
// Helper predicate to define if a value is the maximum in a list
predicate IsMax(l: seq<int>, m: int)
{
  forall i :: 0 <= i < |l| ==> l[i] <= m
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def max_element(l: list)
Return maximum element in the list.
*/
// </vc-description>

// <vc-spec>
method MaxElement(l: seq<int>) returns (m: int)
  requires |l| > 0
  ensures m in l
  ensures IsMax(l, m)
// </vc-spec>
// <vc-code>
{
  m := l[0];
  var i := 1;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant m in l[..i]
    invariant IsMax(l[..i], m)
  {
    if l[i] > m {
      m := l[i];
    }
    i := i + 1;
  }
}
// </vc-code>
