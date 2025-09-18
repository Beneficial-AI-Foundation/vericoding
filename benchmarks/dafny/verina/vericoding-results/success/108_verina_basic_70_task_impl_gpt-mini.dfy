// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): trivial lemma placeholder */
lemma LinearSearch3_Helper() {
}

// </vc-helpers>

// <vc-spec>
method LinearSearch3(a: seq<int>, p: int -> bool) returns (result: nat)
    requires 
        exists i :: 0 <= i < |a| && p(a[i])
    ensures 
        result < |a| &&
        p(a[result]) &&
        forall k :: 0 <= k < result ==> !p(a[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): implement linear search with loop and invariants (removed semicolons) */
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> !p(a[k])
    decreases |a| - i
  {
    if p(a[i]) {
      result := i;
      return;
    }
    i := i + 1;
  }
  // Contradiction with precondition ensures this point is unreachable
  assert false;
}

// </vc-code>
