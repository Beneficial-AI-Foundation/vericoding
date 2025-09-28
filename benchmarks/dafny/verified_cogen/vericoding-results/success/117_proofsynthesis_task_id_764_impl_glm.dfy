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
/* helper modified by LLM (iteration 2): added lemma to prove bounds on CountDigitsRecursively */
lemma CountDigitsRecursivelyBounds(s: seq<char>)
    ensures 0 <= CountDigitsRecursively(s) <= |s|
{
    if |s| == 0 {
        // Base case: empty sequence -> count is 0, which is between 0 and 0.
    } else {
        // Recursive case: get the prefix without the last character.
        var prefix := s[..|s|-1];
        // By induction, the property holds for the prefix.
        CountDigitsRecursivelyBounds(prefix);
        // Now, let c be the last character.
        // The count for s is: CountDigitsRecursively(prefix) + (if IsDigit(s[|s|-1]) then 1 else 0)
        // From the lemma call, we have: 0 <= CountDigitsRecursively(prefix) <= |prefix| = |s| - 1.
        // Therefore, adding 0 or 1 gives a value between 0 and |s|.
    }
}
// </vc-helpers>

// <vc-spec>
method CountDigits(text: array<char>) returns (count: int)
    ensures 0 <= count <= text.Length
    ensures CountDigitsRecursively(text[..]) == count
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added lemma call to prove bounds */
  count := CountDigitsRecursively(text[..]);
  CountDigitsRecursivelyBounds(text[..]);
}
// </vc-code>
