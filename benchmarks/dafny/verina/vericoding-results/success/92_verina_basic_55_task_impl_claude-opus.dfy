// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method compare(a: int, b: int) returns (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false)
// </vc-spec>
// <vc-code>
{
    // impl-start
    result := a == b;
    // impl-end
}
// </vc-code>
