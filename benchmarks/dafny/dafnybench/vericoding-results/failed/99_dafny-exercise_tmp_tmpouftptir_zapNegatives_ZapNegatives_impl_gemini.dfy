// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
                                            else a[i] == old(a[i])
ensures a.Length == old(a).Length
// </vc-spec>
// <vc-code>
{ 
  /* code modified by LLM (iteration 5): removed syntactically incorrect invariant */
  ghost var old_a_seq := a[..];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant a.Length == old_a_seq.Length
    invariant forall k :: 0 <= k < i ==> (if old_a_seq[k] < 0 then a[k] == 0 else a[k] == old_a_seq[k])
    invariant forall k :: i <= k < a.Length ==> a[k] == old_a_seq[k]
  {
    if a[i] < 0 {
      a[i] := 0;
    }
    i := i + 1;
  }
}
// </vc-code>
