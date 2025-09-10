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
lemma CountCharSlice(s: string, c: char, start: nat)
    requires start <= |s|
    ensures CountChar(s, c) == CountChar(s[..start], c) + CountChar(s[start..], c)
    decreases |s| - start
{
    if start == |s| {
        assert s[..start] == s;
        assert s[start..] == "";
        CountCharEmpty(c);
    } else if start < |s| {
        CountCharSlice(s[1..], c, if start > 0 then start - 1 else 0);
    }
}

lemma CountCharEmpty(c: char)
    ensures CountChar("", c) == 0
{
}

lemma CountCharConcat(s1: string, s2: string, c: char)
    ensures CountChar(s1 + s2, c) == CountChar(s1, c) + CountChar(s2, c)
    decreases |s1|
{
    if |s1| == 0 {
        assert s1 == "" && s1 + s2 == s2;
    } else {
        CountCharConcat(s1[1..], s2, c);
    }
}

lemma CountCharSingleChar(c1: char, c2: char)
    ensures CountChar([c1], c2) == (if c1 == c2 then 1 else 0)
{
}

lemma CountCharCharDiffPos(s: string, c: char, pos: int)
    requires 0 <= pos < |s|
    ensures CountChar(s, c) == CountChar(s[..pos], c) + CountChar([s[pos]], c) + CountChar(s[pos+1..], c)
{
    CountCharSlice(s, c, pos);
    assert s[..pos] + [s[pos]] == s[..pos+1];
    CountCharSlice(s, c, pos+1);
    CountCharConcat(s[..pos], [s[pos]], c);
}

ghost function CountCharSliceProperty(s: string, i: int, c: char): int
    requires 0 <= i <= |s|
    ensures CountChar(s[..i+1], c) == CountChar(s[..i], c) + (if i < |s| && s[i] == c then 1 else 0)
{
    if i < |s| then
        (if s[i] == c then 1 else 0)
    else
        0
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == CalculateSum(s)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == CountChar(s[..i], '+') - CountChar(s[..i], '-')
        decreases |s| - i
    {
        if s[i] == '+' {
            count := count + 1;
        } else if s[i] == '-' {
            count := count - 1;
        }
        assert CountChar(s[..i+1], '+') == CountChar(s[..i], '+') + (if s[i] == '+' then 1 else 0);
        assert CountChar(s[..i+1], '-') == CountChar(s[..i], '-') + (if s[i] == '-' then 1 else 0);
        i := i + 1;
    }
    result := count;
}
// </vc-code>

