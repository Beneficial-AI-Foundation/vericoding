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

method Prod(a: array<int>) returns (result: int)
  ensures result == ProdSpec(a[..])
{
  /* code modified by LLM (iteration 5): implementing cumulative product using loop with invariants */
  result := 1;
  for i := 0 to a.Length-1
    invariant result == ProdSpecHelper(a[..], 0, i)
  {
    result := result * a[i];
  }
}

method ProdArray(a: array<int>, start: int, finish: int) returns (result: int)
  requires 0 <= start <= finish <= a.Length
  ensures result == ProdArraySpec(a[..], start, finish)
{
  result := 1;
  for i := start to finish-1
    invariant result == ProdSpecHelper(a[..], start, i)
  {
    result := result * a[i];
  }
}
// </vc-code>
