// <vc-preamble>
predicate ValidInput(s: string) 
{
    |s| >= 3 && |s| <= 100000 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOperationCount(k: int)
{
    0 <= k <= 30
}

predicate ValidOperationFormat(op: string)
{
    (|op| >= 3 && op[0..2] == "L " && IsDigitString(op[2..])) ||
    (|op| >= 3 && op[0..2] == "R " && IsDigitString(op[2..]))
}

predicate IsDigitString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 && '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int)
    else if |s| > 1 && '0' <= s[0] <= '9' then StringToInt(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
    else 0
}

predicate ValidResult(result: seq<string>, s: string)
{
    |result| >= 1 &&
    var k := StringToInt(result[0]);
    ValidOperationCount(k) &&
    |result| == k + 1 &&
    (forall i :: 1 <= i <= k ==> ValidOperationFormat(result[i]))
}
// </vc-preamble>

// <vc-helpers>
function IntToString(n: int): string
    decreases if n < 0 then 1 else 0, if n >= 0 then n else -n
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToString(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

lemma IntToStringIsDigitString(n: int)
    requires n >= 0
    ensures IsDigitString(IntToString(n))
{
    if n == 0 {
    } else {
        IntToStringHelperIsDigitString(n);
    }
}

lemma IntToStringHelperIsDigitString(n: int)
    requires n > 0
    ensures IsDigitString(IntToStringHelper(n))
    decreases n
{
    if n < 10 {
    } else {
        IntToStringHelperIsDigitString(n / 10);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: seq<string>)
    requires ValidInput(s)
    ensures ValidResult(result, s)
// </vc-spec>
// <vc-code>
{
    var l := |s|;
    IntToStringIsDigitString(2 * l - 1);
    var tmpCall1 := IntToString(2 * l - 1);
    result := ["3", "L 2", "R 2", "R " + tmpCall1];
}
// </vc-code>
