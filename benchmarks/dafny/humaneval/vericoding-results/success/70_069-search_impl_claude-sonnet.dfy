// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove set cardinality invariant */
lemma SetCardinalityLemma(s: seq<int>, x: int, i: int, count: int)
  requires 0 <= i < |s|
  requires count == |(set j | 0 <= j < i && s[j] == x)|
  ensures (if s[i] == x then count + 1 else count) == |(set j | 0 <= j < i + 1 && s[j] == x)|
{
  var oldSet := set j | 0 <= j < i && s[j] == x;
  var newSet := set j | 0 <= j < i + 1 && s[j] == x;
  
  if s[i] == x {
    assert newSet == oldSet + {i};
    assert i !in oldSet;
    assert |newSet| == |oldSet| + 1;
  } else {
    assert newSet == oldSet;
  }
}
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)

    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added lemma call to prove invariant maintenance */
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && s[j] == x)|
  {
    SetCardinalityLemma(s, x, i, count);
    if s[i] == x {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
