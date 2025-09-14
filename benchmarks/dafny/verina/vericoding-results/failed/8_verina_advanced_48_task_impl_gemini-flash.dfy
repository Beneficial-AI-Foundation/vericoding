// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): The problem was a misplaced semicolon. The trait definition itself was correct, but the semicolon was inside the curly braces of the function signature rather than after the entire function declaration. Removing the semicolon from inside the fn definition resolves the compilation error. */
trait Split<'T> { fn Split(s: seq<'T>, mid: nat) : (seq<'T>, seq<'T>) }
// </vc-helpers>

// <vc-spec>
method MergeSort(list: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |list| &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]) &&
        multiset(result) == multiset(list)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The error was a compilation error in a helper function definition in vc-helpers section. After fixing the helper, current code will be resubmitted without modifications. */
{
    if |list| <= 1 {
        return list;
    }

    var mid := |list| / 2;
    var left := list[0..mid];
    var right := list[mid..|list|];

    var sortedLeft := MergeSort(left);
    var sortedRight := MergeSort(right);

    var i := 0;
    var j := 0;
    var res_arr := new int[|list|];
    var k := 0;

    while i < |sortedLeft| && j < |sortedRight|
        invariant 0 <= i <= |sortedLeft|
        invariant 0 <= j <= |sortedRight|
        invariant 0 <= k == i + j <= |list|
        invariant forall x, y :: 0 <= x < y < k ==> res_arr[x] <= res_arr[y]
        invariant multiset(res_arr[0..k]) + multiset(sortedLeft[i..]) + multiset(sortedRight[j..]) == multiset(sortedLeft) + multiset(sortedRight)
    {
        if sortedLeft[i] <= sortedRight[j] {
            res_arr[k] := sortedLeft[i];
            i := i + 1;
        } else {
            res_arr[k] := sortedRight[j];
            j := j + 1;
        }
        k := k + 1;
    }

    while i < |sortedLeft|
        invariant 0 <= i <= |sortedLeft|
        invariant 0 <= k == i + j <= |list|
        invariant forall x, y :: 0 <= x < y < k ==> res_arr[x] <= res_arr[y]
        invariant multiset(res_arr[0..k]) + multiset(sortedLeft[i..]) + multiset(sortedRight[j..]) == multiset(sortedLeft) + multiset(sortedRight)
    {
        res_arr[k] := sortedLeft[i];
        i := i + 1;
        k := k + 1;
    }

    while j < |sortedRight|
        invariant 0 <= j <= |sortedRight|
        invariant 0 <= k == i + j <= |list|
        invariant forall x, y :: 0 <= x < y < k ==> res_arr[x] <= res_arr[y]
        invariant multiset(res_arr[0..k]) + multiset(sortedLeft[i..]) + multiset(sortedRight[j..]) == multiset(sortedLeft) + multiset(sortedRight)
    {
        res_arr[k] := sortedRight[j];
        j := j + 1;
        k := k + 1;
    }
    
    result := res_arr[0..];
}
// </vc-code>
