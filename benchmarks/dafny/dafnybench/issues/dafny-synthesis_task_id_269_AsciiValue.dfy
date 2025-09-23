// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
// </vc-spec>
// <vc-code>
{
    ascii := c as int;
}
// </vc-code>
