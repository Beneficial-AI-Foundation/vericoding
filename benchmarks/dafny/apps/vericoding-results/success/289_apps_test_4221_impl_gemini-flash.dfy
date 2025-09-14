predicate ValidInput(s: string) 
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate CorrectPlural(s: string, result: string)
{
    if |s| > 0 && s[|s| - 1] == 's' then
        result == s + "es"
    else
        result == s + "s"
}

// <vc-helpers>
lemma CorrectPluralChar(s: string)
  requires ValidInput(s)
  ensures (s[|s|-1] == 's') == ('a' <= s[|s|-1] <= 'z' && s[|s|-1] == 's')
{}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectPlural(s, result)
// </vc-spec>
// <vc-code>
{
  if s[|s| - 1] == 's'
  {
    result := s + "es";
  }
  else
  {
    result := s + "s";
  }
  
  // CorrectPluralChar(s); // This lemma call helps Dafny reason about the properties of s[|s|-1] - Not needed, simple enough for Dafny
}
// </vc-code>

