// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): fixed syntax error by removing 'then' in if statement */
  var i: nat := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> !p(a[k])
  {
    if (p(a[i])) {
      break;
    }
    i := i + 1;
  }
  result := i;
}
// </vc-code>
