// <vc-preamble>
predicate IsOdd(x: int)
{
    x % 2 != 0
}

datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindFirstOdd(a: array<int>) returns (result: Option<nat>)
    requires a.Length > 0
    ensures
        match result {
            case Some(idx) => idx < a.Length && IsOdd(a[idx]) &&
                forall j :: 0 <= j < idx ==> !IsOdd(a[j])
            case None => forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
        }
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    assume {:axiom} false;
    return None;
}
// </vc-code>
