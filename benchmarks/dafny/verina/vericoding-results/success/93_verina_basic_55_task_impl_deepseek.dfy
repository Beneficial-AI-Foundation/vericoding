// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method compareHelper(a: int, b: int) returns (result: bool)
    ensures (a == b ==> result == true) && (a != b ==> result == false)
{
    result := a == b;
}
// </vc-helpers>

// <vc-spec>
method compare(a: int, b: int) returns (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Call helper function to fix duplicate method error */
  result := compareHelper(a, b);
}
// </vc-code>
