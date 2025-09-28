// <vc-preamble>

function CharSet(s: string): set<char>
{
    set c | c in s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed compilation error */
function CharSet_Equal(s0: string, s1: string): bool
{
    CharSet(s0) == CharSet(s1)
}
// </vc-helpers>

// <vc-spec>
method same_chars(s0: string, s1: string) returns (result: bool)
    ensures result == (CharSet(s0) == CharSet(s1))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed compilation error */
{
    result := CharSet_Equal(s0, s1);
}
// </vc-code>
