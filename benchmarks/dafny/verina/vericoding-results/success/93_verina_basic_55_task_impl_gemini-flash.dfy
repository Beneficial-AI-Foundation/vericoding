// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed 'returns (b: bool)' from predicate declaration as it's implicit. */
predicate IsEqual(x: int, y: int)
{
  x == y
}
// </vc-helpers>

// <vc-spec>
method compare(a: int, b: int) returns (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented the comparison logic directly. */
{
    result := a == b;
}
// </vc-code>
