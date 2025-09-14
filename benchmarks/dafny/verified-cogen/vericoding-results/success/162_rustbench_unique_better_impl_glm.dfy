// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsStrictlyIncreasing(s: seq<int>) {
    forall i: int, j: int :: 0 <= i && i < j && j < |s| ==> s[i] < s[j]
}
/* helper modified by LLM (iteration 3): added last function to get last element of sequence */
function last(s: seq<int>): int
    requires |s| > 0
{
    s[|s| - 1]
}
// </vc-helpers>

// <vc-spec>
method UniqueBetter(a: array<int>) returns (result: seq<int>)
    requires
        forall i: int, j: int ::
            0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures
        forall i: int, j: int ::
            0 <= i && i < j && j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed unresolved identifier by adding last function */
{
    var uniqueSeq := [];
    if a.Length > 0 {
        uniqueSeq := [a[0]];
        var i := 1;
        while i < a.Length
            invariant 0 <= i <= a.Length
            invariant IsStrictlyIncreasing(uniqueSeq)
        {
            if |uniqueSeq| == 0 || last(uniqueSeq) < a[i] {
                uniqueSeq := uniqueSeq + [a[i]];
            }
            i := i + 1;
        }
    }
    result := uniqueSeq;
}
// </vc-code>
