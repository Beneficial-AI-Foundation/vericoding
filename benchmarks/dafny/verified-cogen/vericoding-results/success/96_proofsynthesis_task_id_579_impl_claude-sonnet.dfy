// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InSeq(x: int, s: seq<int>): bool { x in s }

function NotInResult(x: int, result: seq<int>): bool { !(x in result) }

function IsDistinct(s: seq<int>): bool {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}
// </vc-helpers>

// <vc-spec>
method FindDissimilar(arr1: seq<int>, arr2: seq<int>) returns (result: seq<int>)
    ensures
        (forall i :: 0 <= i < |arr1| ==> (!(arr1[i] in arr2) ==> (arr1[i] in result)))
    ensures
        (forall i :: 0 <= i < |arr2| ==> (!(arr2[i] in arr1) ==> (arr2[i] in result)))
    ensures
        (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |arr1|
        invariant 0 <= i <= |arr1|
        invariant forall k :: 0 <= k < i ==> (!(arr1[k] in arr2) ==> (arr1[k] in result))
        invariant forall x :: x in result ==> (x in arr1 && !(x in arr2)) || (x in arr2 && !(x in arr1))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        if !(arr1[i] in arr2) && !(arr1[i] in result) {
            result := result + [arr1[i]];
        }
        i := i + 1;
    }
    i := 0;
    while i < |arr2|
        invariant 0 <= i <= |arr2|
        invariant forall k :: 0 <= k < |arr1| ==> (!(arr1[k] in arr2) ==> (arr1[k] in result))
        invariant forall k :: 0 <= k < i ==> (!(arr2[k] in arr1) ==> (arr2[k] in result))
        invariant forall x :: x in result ==> (x in arr1 && !(x in arr2)) || (x in arr2 && !(x in arr1))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        if !(arr2[i] in arr1) && !(arr2[i] in result) {
            result := result + [arr2[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
