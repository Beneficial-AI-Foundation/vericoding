// <vc-preamble>
predicate IsLowerCase(c: char)
{
    (c as int) >= 97 && (c as int) <= 122
}

predicate IsUpperCase(c: char)
{
    (c as int) >= 65 && (c as int) <= 90
}

function CountUppercaseRecursively(s: seq<char>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountUppercaseRecursively(s[..|s|-1]) + (if IsUpperCase(s[|s|-1]) then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
lemma CountUppercaseRecBounds(s: seq<char>)
    ensures 0 <= CountUppercaseRecursively(s) <= |s|
    decreases |s|
{
    if |s| == 0 {
    } else {
        var n := |s|;
        var s' := s[..n-1];
        CountUppercaseRecBounds(s');
        var last := s[n-1];
        assert CountUppercaseRecursively(s) == CountUppercaseRecursively(s') + (if IsUpperCase(last) then 1 else 0);
        assert 0 <= CountUppercaseRecursively(s');
        assert CountUppercaseRecursively(s') <= |s'|;
        assert CountUppercaseRecursively(s) >= 0;
        assert CountUppercaseRecursively(s) <= |s'| + 1;
        assert |s'| + 1 == |s|;
    }
}
// </vc-helpers>

// <vc-spec>
method CountUppercase(text: array<char>) returns (count: nat)
    ensures 0 <= count <= text.Length
    ensures CountUppercaseRecursively(text[..]) == count as int
// </vc-spec>
// <vc-code>
{
    var c := CountUppercaseRecursively(text[..]);
    CountUppercaseRecBounds(text[..]);
    assert 0 <= c <= text.Length;
    count := c;
}
// </vc-code>
