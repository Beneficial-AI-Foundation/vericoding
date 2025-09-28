// <vc-preamble>

function CharSet(s: string): set<char>
{
    set c | c in s
}
// </vc-preamble>

// <vc-helpers>

function count(c: char, s: string): nat {
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + count(c, s[1..])
}

predicate chars_equal(s0: string, s1: string) {
  /* helper modified by LLM (iteration 3): Simplified to only check character presence */
  (forall c :: c in CharSet(s0) <==> c in CharSet(s1))
}

// </vc-helpers>

// <vc-spec>
method same_chars(s0: string, s1: string) returns (result: bool)
    ensures result == (CharSet(s0) == CharSet(s1))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Direct comparison of character sets */
  result := CharSet(s0) == CharSet(s1);
}
// </vc-code>
