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
    requires forall i :: 0 <= i < |s| ==> s[i] == '+' || s[i] == '-'
    ensures CountChar(s, '+') + CountChar(s, '-') == |s|
{
    if |s| == 0 {
    } else {
        CountCharSum(s[1..]);
    }
}

lemma CountCharSliceExtend(s: string, i: int, c: char)
    requires 0 <= i < |s|
    ensures CountChar(s[..i+1], c) == CountChar(s[..i], c) + (if s[i] == c then 1 else 0)
{
    assert s[..i+1] == s[..i] + [s[i]];
    CountCharAppendOne(s[..i], s[i], c);
}

lemma CountCharAppendOne(s: string, ch: char, c: char)
    ensures CountChar(s + [ch], c) == CountChar(s, c) + (if ch == c then 1 else 0)
{
    if |s| == 0 {
        assert s + [ch] == [ch];
    } else {
        assert s + [ch] == [s[0]] + (s[1..] + [ch]);
        CountCharAppendOne(s[1..], ch, c);
    }
}

lemma CountCharFullString(s: string)
    requires ValidInput(s)
    ensures CountChar(s, '+') == CountChar(s[..|s|], '+')
    ensures CountChar(s, '-') == CountChar(s[..|s|], '-')
{
    assert s[..|s|] == s;
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
        CountCharSliceExtend(s, i, '+');
        CountCharSliceExtend(s, i, '-');
        if s[i] == '+' {
            result := result + 1;
        } else {
            result := result - 1;
        }
        i := i + 1;
    }
    CountCharFullString(s);
}
// </vc-code>

