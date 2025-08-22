// ============ Spec Dependencies ===============

datatype Option<T> = None | Some(value: T)

ghost predicate findSmallest_precond(s: seq<nat>) {
    true
}

ghost predicate findSmallest_postcond(s: seq<nat>, result: Option<nat>)
    requires findSmallest_precond(s)
{
    (result == None ==> |s| == 0) &&
    (result.Some? ==> result.value in s && (forall x :: x in s ==> result.value <= x))
}

// =========================================


// =========== LLM helpers ================
// =========================================


// =========== Main Task ===================

method FindSmallest(s: seq<nat>) returns (result: Option<nat>)
  ensures match result
    case None => |s| == 0
    case Some(r) => r in s && (forall x :: x in s ==> r <= x)
{
    assume(false);
}


// =========================================