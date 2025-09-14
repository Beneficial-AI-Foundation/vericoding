// <vc-preamble>
predicate IsAlphanumeric(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c <= '9')
}

function ToLowercase(c: char): char
{
    if 'A' <= c <= 'Z' then
        ((c as int) + 32) as char
    else
        c
}

function FilterAlphanumeric(s: seq<char>): seq<char>
{
    if |s| == 0 then []
    else if IsAlphanumeric(s[0]) then [ToLowercase(s[0])] + FilterAlphanumeric(s[1..])
    else FilterAlphanumeric(s[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added index guard in seq to prevent out-of-range access */
function ReverseChars(s: seq<char>): seq<char> {
  seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i])
}
// </vc-helpers>

// <vc-spec>
method PalindromeIgnoreNonAlnum(s: string) returns (result: bool)
    ensures 
        result <==> (
            var cleaned := FilterAlphanumeric(s[..]);
            var backward := seq(|cleaned|, i requires 0 <= i < |cleaned| => cleaned[|cleaned| - 1 - i]);
            cleaned == backward
        )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Compute cleaned sequence and its reverse, then compare */
  var cleaned := FilterAlphanumeric(s[..]);
  var backward := seq(|cleaned|, i requires 0 <= i < |cleaned| => cleaned[|cleaned| - 1 - i]);
  result := cleaned == backward;
}
// </vc-code>
