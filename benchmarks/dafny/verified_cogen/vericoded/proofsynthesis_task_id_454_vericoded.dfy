// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsZ(text: array<char>) returns (result: bool)
    ensures result == (exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z'))
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant result == (exists j :: 0 <= j < i && (text[j] == 'Z' || text[j] == 'z'))
  {
    if text[i] == 'Z' || text[i] == 'z' {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>
