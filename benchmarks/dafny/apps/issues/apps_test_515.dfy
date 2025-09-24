// <vc-preamble>
function DigitLoops(d: char): int
{
    if d == '0' then 1
    else if d == '1' || d == '2' || d == '3' || d == '5' || d == '7' then 0
    else if d == '4' || d == '6' || d == '9' then 1
    else if d == '8' then 2
    else 0
}

function StringLoops(s: string): int
{
    if |s| == 0 then 0
    else DigitLoops(s[0]) + StringLoops(s[1..])
}

predicate ValidInput(k: int)
{
    k >= 1
}

predicate ValidSolution(k: int, result: string)
{
    if result == "-1\n" then
        k / 2 + k % 2 > 18
    else
        k / 2 + k % 2 <= 18 &&
        |result| >= 2 &&
        result[|result|-1] == '\n' &&
        StringLoops(result[..|result|-1]) == k &&
        |result[..|result|-1]| <= 18 &&
        |result[..|result|-1]| >= 1 &&
        forall i :: 0 <= i < |result[..|result|-1]| ==> result[i] in "0123456789"
}
// </vc-preamble>

// <vc-helpers>
lemma StringLoopsAppend(s1: string, s2: string)
    ensures StringLoops(s1 + s2) == StringLoops(s1) + StringLoops(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        StringLoopsAppend(s1[1..], s2);
    }
}

lemma StringLoopsEights(n: int)
    requires n >= 0
    ensures StringLoops(seq(n, i => '8')) == 2 * n
{
    if n == 0 {
        assert seq(0, i => '8') == "";
    } else {
        assert seq(n, i => '8') == seq(n-1, i => '8') + "8";
        StringLoopsAppend(seq(n-1, i => '8'), "8");
        StringLoopsEights(n-1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int) returns (result: string)
    requires ValidInput(k)
    ensures ValidSolution(k, result)
// </vc-spec>
// <vc-code>
{
    if k / 2 + k % 2 > 18 {
        result := "-1\n";
    } else {
        var eights := k / 2;
        var needSix := k % 2 == 1;

        result := "";
        var i := 0;
        while i < eights
            invariant 0 <= i <= eights
            invariant result == seq(i, j => '8')
            invariant StringLoops(result) == 2 * i
        {
            result := result + "8";
            StringLoopsAppend(result[..|result|-1], "8");
            i := i + 1;
        }
        
        StringLoopsEights(eights);
        assert StringLoops(result) == 2 * eights;

        if needSix {
            StringLoopsAppend(result, "6");
            result := result + "6";
            assert StringLoops(result) == 2 * eights + 1;
        }

        assert StringLoops(result) == 2 * eights + (if needSix then 1 else 0);
        assert 2 * eights + (if needSix then 1 else 0) == k;

        result := result + "\n";
    }
}
// </vc-code>
