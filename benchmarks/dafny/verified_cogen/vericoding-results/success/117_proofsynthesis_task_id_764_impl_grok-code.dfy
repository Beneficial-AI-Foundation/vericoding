// <vc-preamble>
predicate IsDigit(c: char)
{
    (c as int) >= 48 && (c as int) <= 57
}

function CountDigitsRecursively(s: seq<char>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountDigitsRecursively(s[..|s|-1]) + (if IsDigit(s[|s|-1]) then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to prove bounds of CountDigitsRecursively */
lemma CountDigitsBounds(s: seq<char>)
    ensures 0 <= CountDigitsRecursively(s) <= |s|
{
    if |s| == 0 {
        // trivial
    } else {
        CountDigitsBounds(s[..|s|-1]);
        // inductive step: 0 <= recursive count <= |s|-1, plus 0 or 1
    }
}
// </vc-helpers>

// <vc-spec>
method CountDigits(text: array<char>) returns (count: int)
    ensures 0 <= count <= text.Length
    ensures CountDigitsRecursively(text[..]) == count
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added lemma call to establish bounds before computing count */
{
    CountDigitsBounds(text[..]);
    count := CountDigitsRecursively(text[..]);
}
// </vc-code>
