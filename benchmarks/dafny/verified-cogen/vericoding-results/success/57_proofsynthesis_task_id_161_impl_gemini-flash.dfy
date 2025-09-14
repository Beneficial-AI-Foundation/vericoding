// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveElements(arr1: array<int>, arr2: array<int>) returns (result: seq<int>)
    ensures
        forall i: int ::
            0 <= i < |result| ==> (result[i] in arr1[..] && !(result[i] in arr2[..]))
    ensures
        forall i: int ::
            0 <= i < arr1.Length ==> (arr1[i] in arr2[..] || arr1[i] in result)
// </vc-spec>
// <vc-code>
{
    var s: seq<int> := [];
    var i := 0;
    while i < arr1.Length
        invariant 0 <= i <= arr1.Length
        invariant forall j: int :: 0 <= j < |s| ==> (s[j] in arr1[..] && !(s[j] in arr2[..]))
        invariant forall j: int :: 0 <= j < i ==> (arr1[j] in arr2[..] || arr1[j] in s)
    {
        var foundInArr2 := false;
        var k := 0;
        while k < arr2.Length
            invariant 0 <= k <= arr2.Length
            invariant forall l: int :: 0 <= l < k ==> arr1[i] != arr2[l]
        {
            if arr1[i] == arr2[k] {
                foundInArr2 := true;
                break;
            }
            k := k + 1;
        }

        if !foundInArr2 {
            s := s + [arr1[i]];
        }
        i := i + 1;
    }
    result := s;
}
// </vc-code>
