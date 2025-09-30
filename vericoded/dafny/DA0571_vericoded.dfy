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
lemma CountCharSum(s: string, c: char, i: int)
    requires 0 <= i <= |s|
    ensures CountChar(s[i..], c) == CountChar(s, c) - CountChar(s[..i], c)
{
    if i == 0 {
        assert s[i..] == s;
        assert s[..i] == "";
        assert CountChar("", c) == 0;
    } else if i == |s| {
        assert s[i..] == "";
        assert s[..i] == s;
        assert CountChar("", c) == 0;
    } else {
        // For the recursive case, we decompose differently
        assert s == s[..i] + s[i..];
        CountCharAppend(s[..i], s[i..], c);
        assert CountChar(s, c) == CountChar(s[..i], c) + CountChar(s[i..], c);
    }
}

lemma CountCharAppend(s1: string, s2: string, c: char)
    ensures CountChar(s1 + s2, c) == CountChar(s1, c) + CountChar(s2, c)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        CountCharAppend(s1[1..], s2, c);
    }
}

lemma CountCharPrefix(s: string, c: char, i: int)
    requires 0 <= i <= |s|
    ensures CountChar(s[..i], c) + CountChar(s[i..], c) == CountChar(s, c)
{
    assert s == s[..i] + s[i..];
    CountCharAppend(s[..i], s[i..], c);
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == CalculateSum(s)
// </vc-spec>
// <vc-code>
{
    var plusCount := 0;
    var minusCount := 0;
    var i := 0;
    
    while i < 4
        invariant 0 <= i <= 4
        invariant plusCount == CountChar(s[..i], '+')
        invariant minusCount == CountChar(s[..i], '-')
    {
        if s[i] == '+' {
            plusCount := plusCount + 1;
        } else {
            minusCount := minusCount + 1;
        }
        
        assert s[..i+1] == s[..i] + [s[i]];
        CountCharAppend(s[..i], [s[i]], '+');
        CountCharAppend(s[..i], [s[i]], '-');
        
        i := i + 1;
    }
    
    assert i == 4;
    assert s[..i] == s;
    result := plusCount - minusCount;
}
// </vc-code>

