// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed to pure function (no 'method') to satisfy syntax requirements */
function min(a: nat, b: nat): nat {
  if a <= b then a else b
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
  /* code modified by LLM (iteration 2): implement linear scan to find smallest element with loop invariants */
  if s.Length == 0 {
    result := None;
  } else {
    var minIdx := 0;
    var i := 1;
    while i < s.Length
      invariant 0 <= minIdx < s.Length
      invariant 1 <= i <= s.Length
      invariant forall j :: 0 <= j < i ==> s[minIdx] <= s[j]
      decreases s.Length - i
    {
      if s[i] < s[minIdx] {
        minIdx := i;
      }
      i := i + 1;
    }
    result := Some(s[minIdx]);
  }
}
// </vc-code>
