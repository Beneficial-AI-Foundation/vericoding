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
    result := None;
  } else {
    var min_val := s[0];
    var i := 1;
    while i < s.Length
      invariant 1 <= i <= s.Length
      invariant exists k :: 0 <= k < i && s[k] == min_val
      invariant forall k :: 0 <= k < i ==> min_val <= s[k]
    {
      if s[i] < min_val {
        min_val := s[i];
      }
      i := i + 1;
    }
    result := Some(min_val);
  }
}
// </vc-code>
