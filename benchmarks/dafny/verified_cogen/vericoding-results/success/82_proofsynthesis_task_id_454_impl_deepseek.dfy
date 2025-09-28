// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Add reads clause to function accessing array */
function ArrayHasCharAt(text: array<char>, idx: int): bool
  requires 0 <= idx < text.Length
  reads text
{
  text[idx] == 'Z' || text[idx] == 'z'
}

lemma Lemma_ContainsZ_Empty(text: array<char>)
  requires text.Length == 0
  ensures !(exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z'))
{
}

lemma Lemma_ContainsZ_Char(text: array<char>, idx: int)
  requires 0 <= idx < text.Length
  ensures (exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z')) ==
    ((text[idx] == 'Z' || text[idx] == 'z') || (exists i :: 0 <= i < text.Length && i != idx && (text[i] == 'Z' || text[i] == 'z')))
{
}
// </vc-helpers>

// <vc-spec>
method ContainsZ(text: array<char>) returns (result: bool)
    ensures result == (exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z'))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed verification by ensuring proper invariants */
{
  result := false;
  var i: int := 0;
  
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant !result ==> !(exists j :: 0 <= j < i && (text[j] == 'Z' || text[j] == 'z'))
    invariant result ==> (exists j :: 0 <= j < i && (text[j] == 'Z' || text[j] == 'z'))
  {
    if text[i] == 'Z' || text[i] == 'z' {
      result := true;
    }
    i := i + 1;
  }
  
  if text.Length == 0 {
    Lemma_ContainsZ_Empty(text);
  }
}
// </vc-code>
