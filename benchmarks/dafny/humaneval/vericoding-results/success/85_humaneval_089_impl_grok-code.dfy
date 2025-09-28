// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix syntax errors in if expressions */
function charEncrypt(c: char): char {
  if 'a' <= c <= 'z' then (((c as int - 'a' as int + 4) % 26) + 'a' as int) as char
  else if 'A' <= c <= 'Z' then (((c as int - 'A' as int + 4) % 26) + 'A' as int) as char
  else c
}
// </vc-helpers>

// <vc-spec>
method encrypt(s: string) returns (result: string)
    requires |s| >= 0
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> (
        if 'a' <= s[i] <= 'z' then
            result[i] == (((s[i] as int - 'a' as int + 4) % 26) + 'a' as int) as char
        else if 'A' <= s[i] <= 'Z' then
            result[i] == (((s[i] as int - 'A' as int + 4) % 26) + 'A' as int) as char
        else
            result[i] == s[i]
    )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implement using helper function with seq comprehension */
  result := seq(|s|, i requires 0 <= i < |s| => charEncrypt(s[i]));
}
// </vc-code>
