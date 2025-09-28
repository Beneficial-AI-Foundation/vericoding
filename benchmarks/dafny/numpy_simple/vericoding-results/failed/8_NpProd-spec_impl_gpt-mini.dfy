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
/* helper modified by LLM (iteration 5): lemma for empty range */
lemma ProdSpecHelper_empty(a: seq<int>, start: int)
  requires 0 <= start <= |a|
  ensures ProdSpecHelper(a, start, start) == 1
{
  assert ProdSpecHelper(a, start, start) == 1;
}

/* helper modified by LLM (iteration 5): lemma to extend product by one element at the end */
lemma ProdSpecHelper_extend(a: seq<int>, start: int, i: int)
  requires 0 <= start <= i < |a|
  ensures ProdSpecHelper(a, start, i+1) == ProdSpecHelper(a, start, i) * a[i]
  decreases i - start
{
  if start == i {
    assert ProdSpecHelper(a, i, i+1) == a[i] * ProdSpecHelper(a, i+1, i+1);
    assert ProdSpecHelper(a, i+1, i+1) == 1;
    assert ProdSpecHelper(a, i, i) == 1;
    assert ProdSpecHelper(a, start, i+1) == ProdSpecHelper(a, start, i) * a[i];
  } else {
    assert ProdSpecHelper(a, start, i+1) == a[start] * ProdSpecHelper(a, start+1, i+1);
    ProdSpecHelper_extend(a, start+1, i);
    assert ProdSpecHelper(a, start+1, i+1) == ProdSpecHelper(a, start+1, i) * a[i];
    assert ProdSpecHelper(a, start, i) == a[start] * ProdSpecHelper(a, start+1, i);
    assert ProdSpecHelper(a, start, i+1) == ProdSpecHelper(a, start, i) * a[i];
  }
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
{
  /* code modified by LLM (iteration 5): Prod implemented by delegating to ProdArray */
  result := ProdArray(a, 0, a.Length);
}

{
  /* code modified by LLM (iteration 5): ProdArray implemented with iterative loop and invariants */
  var prod := 1;
  var i := start;
  ProdSpecHelper_empty(a[..], start);
  while i < finish
    invariant 0 <= start <= i <= finish <= a.Length
    invariant prod == ProdSpecHelper(a[..], start, i)
  {
    prod := prod * a[i];
    ProdSpecHelper_extend(a[..], start, i);
    i := i + 1;
  }
  result := prod;
}
// </vc-code>
