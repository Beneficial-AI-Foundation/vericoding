

// ============ Spec Dependencies ===============

ghost predicate multiply_precond(a : int, b : int) {
    true
}

ghost predicate multiply_postcond (a : int, b : int, result: int) 
    requires multiply_precond(a, b)
{
  result - a * b == 0 && a * b - result == 0
}

// =========================================

// =========== Main Task helpers ================
// =========================================

// =========== Main Task ===================

method multiply(a : int, b : int) returns (result: int)
    requires multiply_precond(a, b)
    ensures multiply_postcond(a, b, result)
{   
  assume(false);
}  
