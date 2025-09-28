// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Implemented loop with invariants to verify postcondition */
{
  var i := 0;
  while i < |s| && s[i] != 'z' && s[i] != 'Z'
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] != 'z' && s[k] != 'Z'
  {
    i := i + 1;
  }
  result := i < |s|;
}
// </vc-code>
