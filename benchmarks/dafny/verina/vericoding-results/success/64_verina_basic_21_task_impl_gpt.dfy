// <vc-preamble>
predicate IsSubseqAt(sub: seq<int>, main: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && 
    (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
lemma IsSubseqAtImpliesBounds(sub: seq<int>, main: seq<int>, i: int)
  ensures IsSubseqAt(sub, main, i) ==> 0 <= i && i <= |main| - |sub|
{
}

// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> exists i :: IsSubseqAt(sub, main, i)
// </vc-spec>
// <vc-code>
{
  var found := false;
  var w := 0;
  if |sub| <= |main| {
    var maxStart := |main| - |sub|;
    var i := 0;
    while i <= maxStart
      invariant 0 <= i && i <= maxStart + 1
      invariant found ==> (0 <= w && w < i && IsSubseqAt(sub, main, w))
      invariant found == (exists j: int :: 0 <= j && j < i && IsSubseqAt(sub, main, j))
      decreases maxStart - i + 1
    {
      if IsSubseqAt(sub, main, i) {
        found := true;
        w := i;
      }
      i := i + 1;
    }
    result := found;
  } else {
    result := false;
  }
}
// </vc-code>
