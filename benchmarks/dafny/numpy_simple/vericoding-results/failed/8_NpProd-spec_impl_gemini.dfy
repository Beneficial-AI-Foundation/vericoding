// <vc-preamble>
function ProdSpecHelper(a: seq<int>, start: int, finish: int): int
    requires 0 <= start <= finish <= |a|
    decreases finish - start
{
    if start >= finish then
        1
    else
        a[start] * ProdSpecHelper(a, start + 1, finish)
}

function ProdSpec(a: seq<int>): int {
    ProdSpecHelper(a, 0, |a|)
}

function ProdArraySpec(a: seq<int>, start: int, finish: int): int
    requires 0 <= start <= finish <= |a|
{
    ProdSpecHelper(a, start, finish)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate method to fix compilation error */

// </vc-helpers>

// <vc-spec>
method Prod(a: array<int>) returns (result: int)
    ensures result == ProdSpec(a[..])
{
    assume {:axiom} false;
}

method ProdArray(a: array<int>, start: int, finish: int) returns (result: int)
    requires 0 <= start <= finish <= a.Length
    ensures result == ProdArraySpec(a[..], start, finish)
{
    assume {:axiom} false;
}

lemma {:axiom} ProdTheorem(a: array<int>)
    requires a.Length > 0
    ensures ProdSpec(a[..]) == ProdArraySpec(a[..], 0, a.Length) &&
            (forall i :: 0 <= i < a.Length && a[i] == 0 ==> ProdSpec(a[..]) == 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented ProdArray with an iterative loop */
    if start >= finish {
        result := 1;
    } else {
        result := 1;
        var i := start;
        while i < finish
            invariant start <= i <= finish
            invariant result * ProdSpecHelper(a[..], i, finish) == ProdSpecHelper(a[..], start, finish)
            decreases finish - i
        {
            result := result * a[i];
            i := i + 1;
        }
    }
}

// </vc-code>
