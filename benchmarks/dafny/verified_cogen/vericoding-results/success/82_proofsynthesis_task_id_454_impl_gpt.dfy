// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsZ(c: char) { c == 'Z' || c == 'z' }
// </vc-helpers>

// <vc-spec>
method ContainsZ(text: array<char>) returns (result: bool)
    ensures result == (exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z'))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := false;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant !result
    invariant forall j :: 0 <= j < i ==> (text[j] != 'Z' && text[j] != 'z')
  {
    if text[i] == 'Z' || text[i] == 'z' {
      result := true;
      assert 0 <= i < text.Length;
      assert exists j :: 0 <= j < text.Length && (text[j] == 'Z' || text[j] == 'z');
      return;
    }
    i := i + 1;
  }
  assert i == text.Length;
  assert forall j :: 0 <= j < text.Length ==> (text[j] != 'Z' && text[j] != 'z');
  assert !(exists j :: 0 <= j < text.Length && (text[j] == 'Z' || text[j] == 'z'));
}
// </vc-code>
