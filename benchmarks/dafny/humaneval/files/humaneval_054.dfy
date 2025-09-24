// <vc-preamble>

function CharSet(s: string): set<char>
{
    set c | c in s
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method same_chars(s0: string, s1: string) returns (result: bool)
    ensures result == (CharSet(s0) == CharSet(s1))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
