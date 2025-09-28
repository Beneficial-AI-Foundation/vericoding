// <vc-preamble>
// Looking at the warning, the issue is with the quantifier that lacks a trigger. Since this postcondition is redundant (it's already implied by `|result| == |prototype|`), I'll remove it to fix the compilation issue.



// Method that creates a new sequence with same length as prototype but uninitialized values
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' for compatibility with function-syntax:4; constructs a sequence of zeros of length n */
function zeros(n: int): seq<real>
  requires 0 <= n
  ensures |zeros(n)| == n
  decreases n
{
  if n == 0 then [] else zeros(n - 1) + [0.0]
}
// </vc-helpers>

// <vc-spec>
method numpy_empty_like(prototype: seq<real>) returns (result: seq<real>)
  // No preconditions needed - works with any sequence
  requires true
  // Postconditions ensure structural properties are preserved
  ensures |result| == |prototype|
  // The result is independent of prototype values (only shape matters)
  // Note: We cannot and do not specify what the actual values are since they are uninitialized
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use zeros helper to create a sequence matching prototype length */
  result := zeros(|prototype|);
}
// </vc-code>
