predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

function CountDistinctColors(a: int, b: int, c: int): int
{
    if a == b && b == c then 1
    else if a == b || b == c || a == c then 2
    else 3
}

predicate AllSame(a: int, b: int, c: int)
{
    a == b && b == c
}

predicate ExactlyTwoSame(a: int, b: int, c: int)
{
    (a == b && b != c) || (b == c && a != b) || (a == c && a != b)
}

predicate AllDifferent(a: int, b: int, c: int)
{
    a != b && b != c && a != c
}

// <vc-helpers>
lemma LemmaCountDistinctColors(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures 1 <= CountDistinctColors(a, b, c) <= 3
    ensures CountDistinctColors(a, b, c) == 1 <==> AllSame(a, b, c)
    ensures CountDistinctColors(a, b, c) == 2 <==> ExactlyTwoSame(a, b, c)
    ensures CountDistinctColors(a, b, c) == 3 <==> AllDifferent(a, b, c)
{
    if a == b && b == c {
        calc {
            CountDistinctColors(a, b, c);
            1;
        }
    } else if a == b || b == c || a == c {
        calc {
            CountDistinctColors(a, b, c);
            2;
        }
        assert AllSame(a, b, c) == false;
        if a == b {
            assert ExactlyTwoSame(a, b, c) == (b != c);
        } else if b == c {
            assert ExactlyTwoSame(a, b, c) == (a != b);
        } else {
            assert ExactlyTwoSame(a, b, c) == (a != b);
        }
    } else {
        calc {
            CountDistinctColors(a, b, c);
            3;
        }
        assert ExactlyTwoSame(a, b, c) == false;
        assert AllSame(a, b, c) == false;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures 1 <= result <= 3
    ensures result == CountDistinctColors(a, b, c)
    ensures result == 1 <==> AllSame(a, b, c)
    ensures result == 2 <==> ExactlyTwoSame(a, b, c)
    ensures result == 3 <==> AllDifferent(a, b, c)
// </vc-spec>
// <vc-code>
{
    LemmaCountDistinctColors(a, b, c);
    result := CountDistinctColors(a, b, c);
}
// </vc-code>

