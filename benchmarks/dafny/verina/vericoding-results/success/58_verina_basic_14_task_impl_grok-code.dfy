// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CharIsZ(c: char): bool { c == 'z' || c == 'Z' }
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Changed <=> to <==> in invariants to fix parse errors */
  var i := 0;
  result := false;
  while i < |s| && !result
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && CharIsZ(s[k])
    invariant !result ==> forall k :: 0 <= k < i ==> !CharIsZ(s[k])
  {
    if CharIsZ(s[i]) {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>
