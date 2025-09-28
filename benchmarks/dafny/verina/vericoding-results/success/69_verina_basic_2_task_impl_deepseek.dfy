// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
function IsMin(s: array<nat>, x: nat): bool
  reads s
{
  exists i :: 0 <= i < s.Length && s[i] == x && (forall j :: 0 <= j < s.Length ==> x <= s[j])
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
  /* code modified by LLM (iteration 3): Removed null check, fixed loop invariants */
  if s.Length == 0 {
    result := None;
  } else {
    var min := s[0];
    var idx := 1;
    while idx < s.Length
      invariant 0 <= idx <= s.Length
      invariant exists i :: 0 <= i < idx && s[i] == min
      invariant forall i :: 0 <= i < idx ==> min <= s[i]
    {
      if s[idx] < min {
        min := s[idx];
      }
      idx := idx + 1;
    }
    result := Some(min);
  }
}
// </vc-code>
