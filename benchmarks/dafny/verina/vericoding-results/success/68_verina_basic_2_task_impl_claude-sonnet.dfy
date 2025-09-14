// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
function IsMinimum(s: array<nat>, val: nat): bool
    reads s
{
    (exists i :: 0 <= i < s.Length && s[i] == val) &&
    (forall i :: 0 <= i < s.Length ==> val <= s[i])
}

lemma MinimumExists(s: array<nat>, min_idx: nat)
    requires s.Length > 0
    requires 0 <= min_idx < s.Length
    requires forall i :: 0 <= i < s.Length ==> s[min_idx] <= s[i]
    ensures IsMinimum(s, s[min_idx])
{
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
{
    if s.Length == 0 {
        result := None;
    } else {
        var min_val := s[0];
        var min_idx := 0;
        var i := 1;
        
        while i < s.Length
            invariant 0 <= i <= s.Length
            invariant 0 <= min_idx < i
            invariant min_val == s[min_idx]
            invariant forall j :: 0 <= j < i ==> min_val <= s[j]
        {
            if s[i] < min_val {
                min_val := s[i];
                min_idx := i;
            }
            i := i + 1;
        }
        
        MinimumExists(s, min_idx);
        result := Some(min_val);
    }
}
// </vc-code>
