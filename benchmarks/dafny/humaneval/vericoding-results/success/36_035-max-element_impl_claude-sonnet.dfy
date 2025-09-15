// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)

    requires |l| > 0

    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
// </vc-spec>
// <vc-code>
{
  result := l[0];
  var i := 1;
  while i < |l|
    invariant 1 <= i <= |l|
    invariant forall j :: 0 <= j < i ==> l[j] <= result
    invariant exists j :: 0 <= j < i && l[j] == result
  {
    if l[i] > result {
      result := l[i];
    }
    i := i + 1;
  }
}
// </vc-code>
