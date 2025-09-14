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
  /* code modified by LLM (iteration 2): added minIndex tracking to prove exists postcondition */
  if s.Length == 0 {
    result := None;
  } else {
    var min: nat := s[0];
    var minIndex: nat := 0;
    var i: nat := 1;
    while i < s.Length
      invariant 0 <= i <= s.Length
      invariant 0 <= minIndex < i
      invariant forall j :: 0 <= j < i ==> min <= s[j]
      invariant min == s[minIndex]
      decreases s.Length - i
    {
      if s[i] < min {
        min := s[i];
        minIndex := i;
      }
      i := i + 1;
    }
    result := Some(min);
  }
}
// </vc-code>
