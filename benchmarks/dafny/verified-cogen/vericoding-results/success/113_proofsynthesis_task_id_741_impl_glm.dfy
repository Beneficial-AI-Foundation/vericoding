// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllCharactersSame(char_arr: array<char>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i])
// </vc-spec>
// <vc-code>
{
  if char_arr.Length == 0 {
    result := true;
  } else {
    var i := 1;
    while i < char_arr.Length
      invariant 1 <= i <= char_arr.Length
      invariant forall j :: 1 <= j < i ==> char_arr[0] == char_arr[j]
    {
      if char_arr[0] != char_arr[i] {
        result := false;
        return;
      }
      i := i + 1;
    }
    result := true;
  }
}
// </vc-code>
