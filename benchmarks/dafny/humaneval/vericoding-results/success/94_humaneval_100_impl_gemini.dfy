// <vc-preamble>

predicate ValidInput(n: int)
{
    n > 0
}

predicate ValidPile(pile: seq<int>, n: int)
{
    && |pile| == n
    && (n > 0 ==> |pile| > 0 && pile[0] == n)
    && (forall i :: 0 <= i < |pile| ==> pile[i] == n + 2 * i)
    && (forall i :: 0 <= i < |pile| - 1 ==> pile[i+1] == pile[i] + 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed unresolved identifier 'result' in function ensures clause */
function CreatePile(n: int): seq<int>
    requires ValidInput(n)
    ensures ValidPile(CreatePile(n), n)
{
    seq(n, i => n + 2 * i)
}
// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)
    requires ValidInput(n)
    ensures ValidPile(pile, n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): calling the helper function */
    pile := CreatePile(n);
}
// </vc-code>
