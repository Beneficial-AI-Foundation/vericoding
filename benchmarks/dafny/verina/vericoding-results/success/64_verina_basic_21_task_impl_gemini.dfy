// <vc-preamble>
predicate IsSubseqAt(sub: seq<int>, main: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && 
    (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> exists i :: IsSubseqAt(sub, main, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added if-guard to fix loop invariant-on-entry error. */
  result := false;
  if |sub| <= |main| {
    var i := 0;
    while i <= |main| - |sub| && !result
      invariant 0 <= i <= |main| - |sub| + 1
      invariant result <==> (exists k :: 0 <= k < i && IsSubseqAt(sub, main, k))
    {
      if IsSubseqAt(sub, main, i) {
        result := true;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
