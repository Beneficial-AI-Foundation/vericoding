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
  if s.Length == 0 {
    return None;
  }
  var min_idx := 0;
  var i := 1;
  while i < s.Length
    invariant 0 <= min_idx < i <= s.Length
    invariant forall j :: 0 <= j < i ==> s[min_idx] <= s[j]
  {
    if s[i] < s[min_idx] {
      min_idx := i;
    }
    i := i + 1;
  }
  return Some(s[min_idx]);
}
// </vc-code>
