// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Corrected the comparison operator for 'IsLonger' predicate */
predicate IsLonger(s1: string, s2: string)
{
  (|set c | c in s1|) >= (|set c | c in s2|)
}
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)

    requires |strings| > 0

    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed a parsing error by adding missing curly braces around the 'then' block. */
{
    s := strings[0];
    var i := 1;
    while i < |strings|
      invariant 0 < |strings|
      invariant 0 <= i <= |strings|
      invariant s in strings[..i]
      invariant forall j : int :: 0 <= j < i ==> IsLonger(s, strings[j])
    {
      if !IsLonger(s, strings[i]) {
        s := strings[i];
      }
      i := i + 1;
    }
  }
// </vc-code>
