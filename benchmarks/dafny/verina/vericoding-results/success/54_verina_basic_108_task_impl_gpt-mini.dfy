// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma to satisfy helpers section */
lemma EmptyLemma() ensures true {
}

// </vc-helpers>

// <vc-spec>
method BelowZero(operations: array<int>) returns (result: (array<int>, bool))
    ensures
        result.0.Length == operations.Length + 1
    ensures
        result.0[0] == 0
    ensures
        forall i :: 0 <= i < operations.Length ==> result.0[i + 1] == result.0[i] + operations[i]
    ensures
        result.1 == (exists i :: 1 <= i < result.0.Length && result.0[i] < 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): update neg using disjunction to maintain invariant */
  var n := operations.Length;
  var arr := new int[n + 1];
  arr[0] := 0;
  var i := 0;
  var neg := false;
  while i < n
    invariant 0 <= i <= n
    invariant arr[0] == 0
    invariant forall k :: 0 < k <= i ==> arr[k] == arr[k-1] + operations[k-1]
    invariant neg == (exists k :: 1 <= k <= i && arr[k] < 0)
  {
    arr[i+1] := arr[i] + operations[i];
    neg := neg || (arr[i+1] < 0);
    i := i + 1;
  }
  result := (arr, neg);
}
// </vc-code>
