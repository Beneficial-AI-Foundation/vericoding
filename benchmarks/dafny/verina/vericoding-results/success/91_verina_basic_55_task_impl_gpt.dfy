// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Eq(a: int, b: int): bool { a == b }
// </vc-helpers>

// <vc-spec>
method compare(a: int, b: int) returns (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false)
// </vc-spec>
// <vc-code>
{
  result := Eq(a, b);
}
// </vc-code>
