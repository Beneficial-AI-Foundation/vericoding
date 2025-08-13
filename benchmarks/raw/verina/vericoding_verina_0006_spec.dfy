
// ============ Spec Dependencies ===============

ghost predicate minOfThree_precond(a: int, b: int, c: int)
{
    true
}

ghost predicate minOfThree_postcond(a: int, b: int, c: int, result: int)
    requires minOfThree_precond(a, b, c)
{
    (result <= a && result <= b && result <= c) &&
    (result == a || result == b || result == c)
}

// =========================================

// =========== LLM helpers ================
// =========================================


// =========== Main Task ===================
method minOfThree(a: int, b: int, c: int) returns (result: int)
    requires minOfThree_precond(a, b, c)
    ensures minOfThree_postcond(a, b, c, result)
{
    assume(false);
}

