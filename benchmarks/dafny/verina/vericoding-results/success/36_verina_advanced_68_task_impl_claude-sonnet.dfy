// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed explicit bool return type from predicate */
function CharToDigit(c: char): int
    requires IsDigit(c)
{
    c as int - '0' as int
}

function DigitToChar(n: int): char
    requires 0 <= n <= 9
{
    (n + '0' as int) as char
}

predicate ValidRunLength(s: string)
{
    |s| % 2 == 0 &&
    (forall i :: 0 <= i < |s| ==> 
        (i % 2 == 0 ==> !IsDigit(s[i])) &&
        (i % 2 == 1 ==> IsDigit(s[i])))
}
// </vc-helpers>

// <vc-spec>
lemma RunLengthEncoderProperty(input: string, result: string)
    requires
        // Non-empty check: input is empty iff result is empty
        (|input| == 0) <==> (|result| == 0)
    requires
        // Format validation: result alternates between characters and digits
        |result| > 0 ==> (
            forall i :: 0 <= i < |result| ==> 
                (i % 2 == 0 ==> !IsDigit(result[i])) &&
                (i % 2 == 1 ==> IsDigit(result[i]))
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): maintained proof structure */
    if |input| == 0 {
        assert |result| == 0;
    } else {
        assert |result| > 0;
        assert forall i :: 0 <= i < |result| ==> 
            (i % 2 == 0 ==> !IsDigit(result[i])) &&
            (i % 2 == 1 ==> IsDigit(result[i]));
    }
}
// </vc-code>
