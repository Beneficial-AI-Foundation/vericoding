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
  /* code modified by LLM (iteration 2): Fixed loop bounds to avoid compilation error and added loop invariant for verification. */
  if s.Length == 0 {
    result := None;
  } else {
    var min: nat := s[0];
    if s.Length > 1 {
      var index: int := 1;
      while index < s.Length
        invariant 1 <= index <= s.Length
        invariant min <= s[index - 1]
        invariant forall j :: 0 <= j < index ==> min <= s[j] && exists k :: 0 <= k < index && s[k] == min
      {
        if s[index] < min {
          min := s[index];
        }
        index := index + 1;
      }
    }
    result := Some(min);
  }
}
// </vc-code>
