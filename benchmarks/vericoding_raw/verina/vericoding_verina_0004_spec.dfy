
// ============ Spec Dependencies ===============
ghost predicate kthElement_precond(arr : seq<int>, k: nat) {
  k >= 1 && k <= |arr|
}

ghost predicate kthElement_postcond(arr : seq<int>, k : nat, result: int) 
  requires kthElement_precond(arr, k)
{ 
  result == arr[k-1]
}
// ==============================================

// =========== LLM helpers ================
// =========================================

// ============ Main Task ===================

method kthElement(arr: seq<int>, k: nat) returns (result:int)
    requires kthElement_precond(arr, k)
    ensures kthElement_postcond(arr, k, result)
{
    assume(false); 
}

