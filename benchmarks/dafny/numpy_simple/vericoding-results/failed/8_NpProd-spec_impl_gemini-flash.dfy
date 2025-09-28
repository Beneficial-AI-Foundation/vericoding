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
/* helper modified by LLM (iteration 5): removed `{:recursive}` attribute, as it's not needed for functions with explicit decreases clauses, and fixed capitalization of 'MultArray' to 'multArray' for consistency with Dafny naming conventions */
function multArray(a: array<int>, start: int, finish: int): int
    requires 0 <= start <= finish <= a.Length
    decreases finish - start
{
    if start == finish then
        1
    else
        a[start] * multArray(a, start + 1, finish)
}
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
/* code modified by LLM (iteration 5): fixed compilation error by assigning the result of `multArray` to the `result` variable as required by the method signature. */
{
    result := multArray(a, 0, a.Length);
}
// </vc-code>
