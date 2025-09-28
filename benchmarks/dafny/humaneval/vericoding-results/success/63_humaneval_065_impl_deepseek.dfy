// <vc-preamble>

function intToString(x: int): string
    requires x >= 0
    ensures |intToString(x)| >= 1
    ensures forall i :: 0 <= i < |intToString(x)| ==> '0' <= intToString(x)[i] <= '9'
{
    if x == 0 then "0"
    else intToStringHelper(x, "")
}

function intToStringHelper(x: int, acc: string): string
    requires x >= 0
    requires forall i :: 0 <= i < |acc| ==> '0' <= acc[i] <= '9'
    ensures forall i :: 0 <= i < |intToStringHelper(x, acc)| ==> '0' <= intToStringHelper(x, acc)[i] <= '9'
    ensures x > 0 ==> |intToStringHelper(x, acc)| > |acc|
{
    if x == 0 then acc
    else intToStringHelper(x / 10, [((x % 10) + '0' as int) as char] + acc)
}

function reverseString(s: string): string
    ensures |reverseString(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> reverseString(s)[i] == s[|s| - 1 - i]
{
    if |s| <= 1 then s
    else reverseString(s[1..]) + [s[0]]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed isPositiveNumberString helper */
function isPositiveNumberString(s: string): bool
    ensures isPositiveNumberString(s) <==> (|s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
{
    if |s| == 0 then false
    else forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

lemma DigitsPreservationLemma(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall i :: 0 <= i < |s[start..end]| ==> '0' <= s[start..end][i] <= '9'
{
}

lemma StringLengthLemma(x: int)
    requires x >= 0
    ensures |intToString(x)| >= 1
{
}

lemma NormalizedShiftRangeLemma(shift: int, n: int)
    requires n > 0
    ensures 0 <= shift % n < n
{
}
// </vc-helpers>

// <vc-spec>
method circular_shift(x: int, shift: int) returns (result: string)
    ensures |result| == |intToString(if x < 0 then -x else x)|
    ensures shift > |intToString(if x < 0 then -x else x)| ==> 
            result == reverseString(intToString(if x < 0 then -x else x))
    ensures shift <= |intToString(if x < 0 then -x else x)| && |intToString(if x < 0 then -x else x)| > 0 ==>
            (var digits := intToString(if x < 0 then -x else x);
             var n := |digits|;
             var normalizedShift := shift % n;
             normalizedShift == 0 ==> result == digits)
    ensures shift <= |intToString(if x < 0 then -x else x)| && |intToString(if x < 0 then -x else x)| > 0 ==>
            (var digits := intToString(if x < 0 then -x else x);
             var n := |digits|;
             var normalizedShift := shift % n;
             normalizedShift > 0 ==> result == digits[n - normalizedShift..] + digits[..n - normalizedShift])
    ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed shift comparison and digit preservation */
    var num := if x < 0 then -x else x;
    var digits := intToString(num);
    var n := |digits|;
    
    if n == 0 {
        result := "";
    } else {
        var normalizedShift := shift % n;
        if shift > |intToString(num)| {
            result := reverseString(digits);
        } else if normalizedShift == 0 {
            result := digits;
        } else {
            DigitsPreservationLemma(digits, n - normalizedShift, n);
            DigitsPreservationLemma(digits, 0, n - normalizedShift);
            result := digits[n - normalizedShift..] + digits[..n - normalizedShift];
        }
    }
}
// </vc-code>
