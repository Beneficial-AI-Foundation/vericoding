// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
function Min(a: nat, b: nat): nat { if a < b then a else b }
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
    return;
  }
  var min := s[0];
  var k := 1;
  while k < s.Length
    invariant 1 <= k <= s.Length
    invariant forall j :: 0 <= j < k ==> min <= s[j]
    invariant exists j :: 0 <= j < k && s[j] == min
    decreases s.Length - k
  {
    if s[k] < min {
      min := s[k];
    }
    k := k + 1;
  }
  result := Some(min);
}
// </vc-code>
