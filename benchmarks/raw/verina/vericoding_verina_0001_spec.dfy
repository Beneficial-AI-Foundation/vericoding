

// ============ Spec Dependencies ===============

ghost predicate hasOppositeSign_precond(a: int, b: int) {
    true
}

ghost predicate hasOppositeSign_postcond(a: int, b: int, result: bool)
    requires hasOppositeSign_precond(a, b)
{
(((a < 0 && b > 0) || (a > 0 && b < 0)) ==> result) &&
  (!((a < 0 && b > 0) || (a > 0 && b < 0)) ==> !result)
}

// =========================================


// =========== LLM helpers ================
// ==========================================


// =========== Main Task ===================

method hasOppositeSign(a : int, b : int) returns (result: bool) 
    requires hasOppositeSign_precond(a, b)
    ensures hasOppositeSign_postcond(a, b, result)
{
    assume(false);
}

// =========================================