// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function identity(arr: seq<int>): seq<int> { arr }
// </vc-helpers>

// <vc-spec>
method copy(arr: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |arr| &&
        forall i :: 0 <= i < |arr| ==> result[i] == arr[i]
// </vc-spec>
// <vc-code>
{
  result := arr;
}
// </vc-code>
