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
            var min := s[0];
            for i := 1 to s.Length
                invariant forall j :: 0 <= j < i ==> min <= s[j]
                invariant exists k :: 0 <= k < i && s[k] == min
            {
                if s[i] < min {
                    min := s[i];
                }
            }
            result := Some(min);
        }
// </vc-code>
