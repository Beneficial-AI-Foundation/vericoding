// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArrayConcat(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |a| + |b| &&
        (forall i :: 0 <= i < |a| ==> result[i] == a[i]) &&
        (forall i :: 0 <= i < |b| ==> result[i + |a|] == b[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type mismatch when assigning array to sequence */
{
    var i := 0;
    var res_array := new int[|a| + |b|];

    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall k :: 0 <= k < i ==> res_array[k] == a[k]
    {
        res_array[i] := a[i];
        i := i + 1;
    }
    i := 0;
    while i < |b|
        invariant 0 <= i <= |b|
        invariant forall k :: 0 <= k < |a| ==> res_array[k] == a[k]
        invariant forall k :: 0 <= k < i ==> res_array[k + |a|] == b[k]
    {
        res_array[i + |a|] := b[i];
        i := i + 1;
    }

    result := res_array[..]; // Convert array to sequence
}
// </vc-code>
