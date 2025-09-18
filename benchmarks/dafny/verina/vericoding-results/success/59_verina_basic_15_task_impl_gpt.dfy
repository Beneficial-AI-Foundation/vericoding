// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple predicate to express 'consecutive at index' */
predicate HasConsecutiveAt(a: seq<int>, i: int) { 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1] }
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use direct existential to compute the result safely */
  result := exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1];
}
// </vc-code>
