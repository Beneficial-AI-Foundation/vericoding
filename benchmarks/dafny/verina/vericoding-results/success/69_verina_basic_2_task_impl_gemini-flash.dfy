// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause */
predicate IsSmallest(s: array<nat>, r: nat)
    requires s.Length > 0
    reads s
{
    (exists i :: 0 <= i < s.Length && s[i] == r) &&
    (forall i :: 0 <= i < s.Length ==> r <= s[i])
}
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
/* code modified by LLM (iteration 2): fixed loop invariants to handle new smallest */
{
    if s.Length == 0 {
        result := None;
    } else {
        var smallest: nat := s[0];
        var i: int := 1;
        while i < s.Length
            invariant 0 <= i <= s.Length
            invariant (forall j :: 0 <= j < i ==> smallest <= s[j])
            invariant (exists k :: 0 <= k < i && s[k] == smallest)
        {
            if s[i] < smallest {
                smallest := s[i];
            }
            i := i + 1;
        }
        result := Some(smallest);
    }
}
// </vc-code>
