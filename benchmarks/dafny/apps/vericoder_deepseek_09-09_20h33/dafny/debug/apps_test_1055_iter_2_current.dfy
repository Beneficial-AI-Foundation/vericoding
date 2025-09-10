predicate ValidInput(a: seq<int>)
{
    |a| > 0
}

predicate isSorted(x: seq<int>)
{
    forall i, j :: 0 <= i < j < |x| ==> x[i] <= x[j]
}

function thanosSort(x: seq<int>): int
    requires |x| > 0
    ensures thanosSort(x) >= 1
    ensures thanosSort(x) <= |x|
    ensures isSorted(x) ==> thanosSort(x) == |x|
{
    var len := |x|;
    if isSorted(x) then
        len
    else
        var firstHalf := x[..len/2];
        var secondHalf := x[len/2..];
        var leftResult := thanosSort(firstHalf);
        var rightResult := thanosSort(secondHalf);
        if leftResult > rightResult then leftResult else rightResult
}

// <vc-helpers>
lemma ThanosSortLemma(a: seq<int>)
    requires |a| > 0
    ensures thanosSort(a) >= 1
    ensures thanosSort(a) <= |a|
    ensures isSorted(a) ==> thanosSort(a) == |a|
{
    if isSorted(a) {
    } else {
        var len := |a|;
        var firstHalf := a[..len/2];
        var secondHalf := a[len/2..];
        assert |firstHalf| > 0;
        assert |secondHalf| > 0;
        ThanosSortLemma(firstHalf);
        ThanosSortLemma(secondHalf);
    }
}

lemma ThanosSortPreserved(a: seq<int>, b: seq<int>)
    requires |a| > 0 && |b| > 0
    requires forall i :: 0 <= i < |a| && i < |b| ==> a[i] == b[i]
    ensures thanosSort(a) == thanosSort(b)
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires ValidInput(a)
    ensures result == thanosSort(a)
    ensures 1 <= result <= |a|
// </vc-spec>
// <vc-code>
{
    ThanosSortLemma(a);
    var len := |a|;
    if isSorted(a) {
        result := len;
    } else {
        var firstHalf := a[..len/2];
        var secondHalf := a[len/2..];
        assert |firstHalf| > 0;
        assert |secondHalf| > 0;
        var leftResult := solve(firstHalf);
        var rightResult := solve(secondHalf);
        if leftResult > rightResult {
            result := leftResult;
        } else {
            result := rightResult;
        }
    }
}
// </vc-code>

