// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function RemoveFrontHelper(a: seq<int>): seq<int>
  requires |a| > 0
  ensures |RemoveFrontHelper(a)| == |a| - 1
  ensures forall i :: 0 <= i < |a| - 1 ==> RemoveFrontHelper(a)[i] == a[i + 1]
{
  if |a| == 1 then [] else a[1..]
}

// </vc-helpers>

// <vc-spec>
method RemoveFront(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |a| > 0
    ensures |result| == |a| - 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
  result := RemoveFrontHelper(a);
}
// </vc-code>
