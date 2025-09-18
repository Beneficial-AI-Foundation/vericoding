// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): make parameters nullable to allow null checks */
lemma CopyPrefix(a: array?<int>, r: array?<int>, k: int)
  requires a != null && r != null
  requires 0 <= k <= a.Length
  requires r.Length == a.Length + 1
  requires forall i :: 0 <= i < k ==> r[i] == a[i]
  ensures forall i :: 0 <= i < k ==> r[i] == a[i]
{
}

// </vc-helpers>

// <vc-spec>
method Append(a: array<int>, b: int) returns (result: array<int>)
    ensures result.Length == a.Length + 1
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
    ensures result[a.Length] == b
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): allocate result and copy elements from a, then append b */
  result := new int[a.Length + 1];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j]
  {
    result[i] := a[i];
    i := i + 1;
  }
  result[a.Length] := b;
}

// </vc-code>
