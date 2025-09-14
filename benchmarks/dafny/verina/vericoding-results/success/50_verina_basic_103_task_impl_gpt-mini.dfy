// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): kept index predicate and removed unnecessary null checks from CopyLemma */
predicate ValidIndexRange(n: int, idx: int) { 0 <= idx < n }

/* helper modified by LLM (iteration 2): removed unnecessary null checks from CopyLemma */
lemma CopyLemma(a: array<int>, b: array<int>, n: int)
  requires 0 <= n <= a.Length && a.Length == b.Length
  requires forall i :: 0 <= i < n ==> b[i] == a[i]
  ensures forall i :: 0 <= i < n ==> b[i] == a[i]
{ }

// </vc-helpers>

// <vc-spec>
method update_elements(a: array<int>) returns (result: array<int>)
    requires a.Length >= 8
    ensures result.Length == a.Length
    ensures result[4] == a[4] + 3
    ensures result[7] == 516
    ensures forall i :: 0 <= i < a.Length && i != 4 && i != 7 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): allocate result and copy elements except indices 4 and 7, then set specified updates */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i && k != 4 && k != 7 ==> result[k] == a[k]
  {
    if i != 4 && i != 7 {
      result[i] := a[i];
    }
    i := i + 1;
  }
  // Set the specified updates
  result[4] := a[4] + 3;
  result[7] := 516;
}

// </vc-code>
