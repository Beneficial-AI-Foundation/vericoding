// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
function minNat(a: nat, b: nat): nat { if a <= b then a else b }
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
    var min := s[0];
    var idx := 0;
    var i := 1;
    while i < s.Length
      invariant 0 <= i <= s.Length
      invariant 0 <= idx < i
      invariant min == s[idx]
      invariant forall j :: 0 <= j < i ==> min <= s[j]
    {
      if s[i] < min {
        min := s[i];
        idx := i;
      }
      i := i + 1;
    }
    result := Some(min);
  }
}
// </vc-code>
