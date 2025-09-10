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
lemma allSameImpliesCountIsOne(a: int, b: int, c: int)
    requires AllSame(a, b, c)
    ensures CountDistinctColors(a,b,c) == 1
{ }

lemma exactlyTwoSameImpliesCountIsTwo(a: int, b: int, c: int)
    requires ExactlyTwoSame(a, b, c)
    ensures CountDistinctColors(a, b, c) == 2
{
    if (a == b && b != c) {
        assert a == b;
        assert b != c;
        if (a == c) { // a == b && b !=c && a == c => a == b == c which contradicts b != c
            assert false;
        }
    } else if (b == c && a != b) {
        assert b == c;
        assert a != b;
        if (a == c) { // a != b && b == c && a == c => a == b == c which contradicts a != b
             assert false;
        }
    } else if (a == c && a != b) {
        assert a == c;
        assert a != b;
        if (b == c) { // a != b && b == c && a == c => a == b == c which contradicts a != b
             assert false;
        }
    }
}

lemma allDifferentImpliesCountIsThree(a: int, b: int, c: int)
    requires AllDifferent(a, b, c)
    ensures CountDistinctColors(a, b, c) == 3
{ }

lemma countIsOneImpliesAllSame(a: int, b: int, c: int)
    requires CountDistinctColors(a,b,c) == 1
    ensures AllSame(a, b, c)
{ }

lemma countIsTwoImpliesExactlyTwoSame(a: int, b: int, c: int)
    requires CountDistinctColors(a,b,c) == 2
    ensures ExactlyTwoSame(a, b, c)
{
    if (a == b) { // assuming two distinct colors (so not all same) and a==b, then b must not be equal to c
        assert a == b;
        assert b != c; // If b == c, then a == b == c, implies CountDistinctColors is 1, contradiction.
    } else if (b == c) { // assuming two distinct colors (so not all same) and b==c, then a must not be equal to b
        assert b == c;
        assert a != b; // If a == b, then a == b == c, implies CountDistinctColors is 1, contradiction.
    } else if (a == c) { // assuming two distinct colors (so not all same) and a==c, then a must not be equal to b
        assert a == c;
        assert a != b; // If a == b, then a == b == c, implies CountDistinctColors is 1, contradiction.
    } else { // implies a != b, b != c, a != c, so CountDistinctColors is 3, contradiction.
        assert false;
    }
}

lemma countIsThreeImpliesAllDifferent(a: int, b: int, c: int)
    requires CountDistinctColors(a, b, c) == 3
    ensures AllDifferent(a, b, c)
{ }
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
    if (AllSame(a, b, c)) {
        result := 1;
        allSameImpliesCountIsOne(a, b, c);
        countIsOneImpliesAllSame(a,b,c);
    } else if (ExactlyTwoSame(a, b, c)) {
        result := 2;
        exactlyTwoSameImpliesCountIsTwo(a, b, c);
        countIsTwoImpliesExactlyTwoSame(a,b,c);
    } else {
        // If not AllSame and not ExactlyTwoSame, then it must be AllDifferent
        // We know that (a==b && b==c) || (a==b || b==c || a==c) || (a!=b && b!=c && a!=c) covers all cases uniquely
        // since AllSame implies the first condition, and ExactlyTwoSame implies the second,
        // it must be that the remaining case is AllDifferent.
        assert AllDifferent(a, b, c);
        result := 3;
        allDifferentImpliesCountIsThree(a, b, c);
        countIsThreeImpliesAllDifferent(a,b,c);
    }
}
// </vc-code>

