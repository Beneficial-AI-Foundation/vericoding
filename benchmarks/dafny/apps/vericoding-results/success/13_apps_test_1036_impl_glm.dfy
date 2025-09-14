function winner(a: char, b: char): char
{
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') then b else a
}

predicate validRPSChar(c: char)
{
    c == 'R' || c == 'P' || c == 'S'
}

predicate validRPSString(s: string)
{
    forall i :: 0 <= i < |s| ==> validRPSChar(s[i])
}

predicate ValidInput(n: int, k: int, s: string)
{
    n > 0 && k >= 0 && |s| == n && validRPSString(s)
}

// <vc-helpers>
lemma winner_lemma(a: char, b: char)
    requires validRPSChar(a) && validRPSChar(b)
    ensures validRPSChar(winner(a, b))
{
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') {
        assert b == 'R' || b == 'P' || b == 'S';
    } else {
        assert a == 'R' || a == 'P' || a == 'S';
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
    if k == 0 {
        return s[0];
    }
    var next := s;
    for i := 1 to k
        invariant 1 <= |next|
        invariant validRPSString(next)
    {
        var accum_str: string := "";
        var j := 0;
        while j < |next| - 1
            invariant 0 <= j <= |next|
            invariant j % 2 == 0
            invariant validRPSString(accum_str)
            invariant |accum_str| == j / 2
        {
            winner_lemma(next[j], next[j+1]);
            accum_str := accum_str + [winner(next[j], next[j+1])];
            j := j + 2;
        }
        if j == |next| - 1 {
            accum_str := accum_str + [next[j]];
        }
        next := accum_str;
    }
    return next[0];
}
// </vc-code>

