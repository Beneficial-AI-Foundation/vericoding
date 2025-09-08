Given a string of exactly 4 characters containing only '+' and '-',
calculate the sum where each '+' contributes +1 and each '-' contributes -1.

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

lemma CountCharExtendLemma(prefix: string, c: char, target: char)
    ensures CountChar(prefix + [c], target) == CountChar(prefix, target) + (if c == target then 1 else 0)
{
    if |prefix| == 0 {
        assert prefix == [];
        assert prefix + [c] == [c];
        assert CountChar([c], target) == (if c == target then 1 else 0) + CountChar([], target);
        assert CountChar([], target) == 0;
    } else {
        var rest := prefix[1..];
        CountCharExtendLemma(rest, c, target);
        assert CountChar(rest + [c], target) == CountChar(rest, target) + (if c == target then 1 else 0);
        assert prefix + [c] == [prefix[0]] + (rest + [c]);
        assert CountChar(prefix + [c], target) == (if prefix[0] == target then 1 else 0) + CountChar(rest + [c], target);
        assert CountChar(prefix + [c], target) == (if prefix[0] == target then 1 else 0) + CountChar(rest, target) + (if c == target then 1 else 0);
        assert CountChar(prefix, target) == (if prefix[0] == target then 1 else 0) + CountChar(rest, target);
    }
}

method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == CalculateSum(s)
{
    var plus_count := 0;
    var minus_count := 0;

    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant plus_count == CountChar(s[..i], '+')
        invariant minus_count == CountChar(s[..i], '-')
    {
        CountCharExtendLemma(s[..i], s[i], '+');
        CountCharExtendLemma(s[..i], s[i], '-');

        assert s[..i] + [s[i]] == s[..i+1];
        assert CountChar(s[..i+1], '+') == CountChar(s[..i], '+') + (if s[i] == '+' then 1 else 0);
        assert CountChar(s[..i+1], '-') == CountChar(s[..i], '-') + (if s[i] == '-' then 1 else 0);

        if s[i] == '+' {
            plus_count := plus_count + 1;
            assert plus_count == CountChar(s[..i], '+') + 1;
            assert plus_count == CountChar(s[..i+1], '+');
        } else if s[i] == '-' {
            minus_count := minus_count + 1;
            assert minus_count == CountChar(s[..i], '-') + 1;
            assert minus_count == CountChar(s[..i+1], '-');
        }
    }

    assert s[..|s|] == s;
    result := plus_count - minus_count;
}
