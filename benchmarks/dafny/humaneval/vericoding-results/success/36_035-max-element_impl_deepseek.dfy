// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(l: seq<int>): int
  requires |l| > 0
  ensures forall i :: 0 <= i < |l| ==> l[i] <= max(l)
  ensures exists i :: 0 <= i < |l| && l[i] == max(l)
{
  if |l| == 1 then
    l[0]
  else
    var submax := max(l[1..]);
    if l[0] > submax then
      l[0]
    else
      submax
}
// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)

    requires |l| > 0

    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
// </vc-spec>
// <vc-code>
{
  result := max(l);
}
// </vc-code>
