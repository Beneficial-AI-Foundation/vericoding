// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def max_element(l: list)
Return maximum element in the list.
*/
// </vc-description>

// <vc-spec>
method MaxElement(l: seq<int>) returns (max: int)
  requires |l| > 0
  ensures max in l
  ensures forall x :: x in l ==> x <= max
// </vc-spec>
// <vc-code>
method MaxElement(l: seq<int>) returns (max: int)
  requires |l| > 0
  ensures max in l
  ensures forall x :: x in l ==> x <= max
{
  max := l[0];
  var i := 1;
  while i < |l|
    invariant 1 <= i <= |l|
    invariant max in l
    invariant forall j :: 0 <= j < i ==> l[j] <= max
  {
    if l[i] > max {
      max := l[i];
    }
    i := i + 1;
  }
}
// </vc-code>
