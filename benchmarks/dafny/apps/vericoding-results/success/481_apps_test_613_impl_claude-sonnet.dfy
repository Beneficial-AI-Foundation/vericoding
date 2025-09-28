predicate ValidInput(t: int, a: int, b: int)
{
    t > 0 && a > 0 && b > 0
}

predicate ValidOutput(res: string)
{
    res == "0" || res == "1" || res == "2" || res == "inf"
}

predicate InfiniteCase(t: int, a: int, b: int)
{
    a == t && a == b && a == 1
}

predicate TwoSolutionsCase(t: int, a: int, b: int)
{
    a == t && a == b && a != 1
}

predicate ZeroSolutionsCase(t: int, a: int, b: int)
{
    (t == 2 && a == 3 && b > 10000) ||
    (a == t && a != b) ||
    (a != t && (a - b) % (t - a) == 0) ||
    (a != t && (a - b) % (t - a) != 0 && t == b)
}

predicate OneSolutionCase(t: int, a: int, b: int)
{
    a != t && (a - b) % (t - a) != 0 && t != b
}

// <vc-helpers>
lemma CasesExhaustive(t: int, a: int, b: int)
    requires ValidInput(t, a, b)
    ensures InfiniteCase(t, a, b) || TwoSolutionsCase(t, a, b) || ZeroSolutionsCase(t, a, b) || OneSolutionCase(t, a, b)
{
    if a == t && a == b && a == 1 {
        assert InfiniteCase(t, a, b);
    } else if a == t && a == b && a != 1 {
        assert TwoSolutionsCase(t, a, b);
    } else if (t == 2 && a == 3 && b > 10000) ||
              (a == t && a != b) ||
              (a != t && (a - b) % (t - a) == 0) ||
              (a != t && (a - b) % (t - a) != 0 && t == b) {
        assert ZeroSolutionsCase(t, a, b);
    } else {
        assert OneSolutionCase(t, a, b);
    }
}

lemma CasesMutuallyExclusive(t: int, a: int, b: int)
    requires ValidInput(t, a, b)
    ensures !(InfiniteCase(t, a, b) && TwoSolutionsCase(t, a, b))
    ensures !(InfiniteCase(t, a, b) && ZeroSolutionsCase(t, a, b))
    ensures !(InfiniteCase(t, a, b) && OneSolutionCase(t, a, b))
    ensures !(TwoSolutionsCase(t, a, b) && ZeroSolutionsCase(t, a, b))
    ensures !(TwoSolutionsCase(t, a, b) && OneSolutionCase(t, a, b))
    ensures !(ZeroSolutionsCase(t, a, b) && OneSolutionCase(t, a, b))
{
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, a: int, b: int) returns (res: string)
    requires ValidInput(t, a, b)
    requires t != a || a == t
    ensures ValidOutput(res)
    ensures InfiniteCase(t, a, b) ==> res == "inf"
    ensures TwoSolutionsCase(t, a, b) ==> res == "2"
    ensures ZeroSolutionsCase(t, a, b) ==> res == "0"
    ensures OneSolutionCase(t, a, b) ==> res == "1"
// </vc-spec>
// <vc-code>
{
    CasesExhaustive(t, a, b);
    CasesMutuallyExclusive(t, a, b);
    
    if a == t && a == b && a == 1 {
        res := "inf";
    } else if a == t && a == b && a != 1 {
        res := "2";
    } else if (t == 2 && a == 3 && b > 10000) ||
              (a == t && a != b) ||
              (a != t && (a - b) % (t - a) == 0) ||
              (a != t && (a - b) % (t - a) != 0 && t == b) {
        res := "0";
    } else {
        res := "1";
    }
}
// </vc-code>

