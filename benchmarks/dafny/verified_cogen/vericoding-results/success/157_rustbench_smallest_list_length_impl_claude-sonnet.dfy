// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MinLength(lists: array<array<int>>, upTo: int): int
    requires lists.Length > 0
    requires 0 < upTo <= lists.Length
    reads lists, lists[..]
{
    if upTo == 1 then lists[0].Length
    else
        var prevMin := MinLength(lists, upTo - 1);
        if lists[upTo - 1].Length < prevMin then lists[upTo - 1].Length else prevMin
}

/* helper modified by LLM (iteration 2): removed reads clause from lemma */
lemma MinLengthProperties(lists: array<array<int>>, upTo: int)
    requires lists.Length > 0
    requires 0 < upTo <= lists.Length
    ensures exists i :: 0 <= i < upTo && MinLength(lists, upTo) == lists[i].Length
    ensures forall i :: 0 <= i < upTo ==> MinLength(lists, upTo) <= lists[i].Length
{
    if upTo == 1 {
        assert MinLength(lists, upTo) == lists[0].Length;
    } else {
        MinLengthProperties(lists, upTo - 1);
        var prevMin := MinLength(lists, upTo - 1);
        if lists[upTo - 1].Length < prevMin {
            assert MinLength(lists, upTo) == lists[upTo - 1].Length;
        } else {
            assert MinLength(lists, upTo) == prevMin;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method SmallestListLength(lists: array<array<int>>) returns (result: int)
    requires lists.Length > 0
    ensures exists i :: 0 <= i < lists.Length && result == lists[i].Length
    ensures forall i :: 0 <= i < lists.Length ==> result <= lists[i].Length
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by removing verification bypass */
    MinLengthProperties(lists, lists.Length);
    result := MinLength(lists, lists.Length);
}
// </vc-code>
