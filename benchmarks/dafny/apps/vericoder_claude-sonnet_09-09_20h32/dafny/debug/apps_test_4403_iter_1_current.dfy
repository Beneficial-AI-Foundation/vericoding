predicate ValidInput(s: string) {
    |s| == 4 && forall i :: 0 <= i < |s| ==> s[i] == '+' || s[i] == '-'
}

function CountChar(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function CalculateSum(s: string): int
    requires ValidInput(s)
{
    CountChar(s, '+') - CountChar(s, '-')
}

// <vc-helpers>
lemma CountCharBounds(s: string, c: char)
    ensures 0 <= CountChar(s, c) <= |s|
{
    if |s| == 0 {
    } else {
        CountCharBounds(s[1..], c);
    }
}

lemma CountCharSum(s: string)
    requires ValidInput(s)
    ensures CountChar(s, '+') + CountChar(s, '-') == |s|
{
    if |s| == 0 {
    } else {
        CountCharSum(s[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == CalculateSum(s)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result == CountChar(s[..i], '+') - CountChar(s[..i], '-')
    {
        if s[i] == '+' {
            result := result + 1;
        } else {
            result := result - 1;
        }
        i := i + 1;
    }
}
// </vc-code>

