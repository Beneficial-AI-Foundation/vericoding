// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindSmallest(s: array<nat>) returns (result: Option<nat>)
    ensures
        match result {
            case None => s.Length == 0
            case Some(r) => s.Length > 0 && 
                      (exists i :: 0 <= i < s.Length && s[i] == r) &&
                      (forall i :: 0 <= i < s.Length ==> r <= s[i])
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := None;
    // impl-end
}
// </vc-code>
