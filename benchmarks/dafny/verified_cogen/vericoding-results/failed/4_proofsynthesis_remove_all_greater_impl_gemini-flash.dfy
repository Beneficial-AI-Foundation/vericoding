// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes */
predicate IsInArray(arr: seq<int>, val: int) {
  exists k :: 0 <= k < |arr| && arr[k] == val
}
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)

    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]

    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && result[k] in v[..]
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> v[k] in result[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The first for loop's range was fixed from `0 to v.Length - 1` to `0 to v.Length`, and its invariant `0 <= count <= i` to `0 <= count <= i && count <= v.Length`. The second for loop's invariant was fixed from `0 <= i <= count` to `0 <= i <= result.Length`. */
{
    var tempArray: array<int> := new int[v.Length];
    var count := 0;
    for i := 0 to v.Length
        invariant 0 <= i <= v.Length
        invariant 0 <= count <= i && count <= v.Length
        invariant forall k :: 0 <= k < count ==> tempArray[k] <= e && IsInArray(v[..], tempArray[k])
        invariant forall k :: 0 <= k < i && v[k] <= e ==> IsInArray(tempArray[..count], v[k])
    {
        if i < v.Length && v[i] <= e {
            tempArray[count] := v[i];
            count := count + 1;
        }
    }

    result := new int[count];
    for i := 0 to count - 1
        invariant 0 <= i <= result.Length
        invariant forall k :: 0 <= k < i ==> result[k] == tempArray[k]
    {
        result[i] := tempArray[i];
    }
}
// </vc-code>
