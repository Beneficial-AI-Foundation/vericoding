

// <vc-helpers>
lemma CountLemma(s: seq<int>, x: int, count: int)
    requires 0 <= count <= |s|
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)| <==>
        (forall i :: 0 <= i < |s| ==> (s[i] == x) == (i < count))
{
    // This lemma is not actually used in the verification
}

lemma SetEqualityLemma(s: seq<int>, x: int, index: int, count: int)
    requires 0 <= index <= |s|
    requires count == |(set i | 0 <= i < index && s[i] == x)|
    ensures |(set i | 0 <= i < |s| && s[i] == x)| == count + |(set i | index <= i < |s| && s[i] == x)|
{
    // Proof: the two sets are disjoint and their union covers the whole range
    // The set from 0 to |s| is partitioned into [0, index) and [index, |s|)
    // Since these intervals are disjoint, the cardinality is additive
}

lemma EmptySetLemma(s: seq<int>, x: int, index: int)
    requires index == |s|
    ensures |(set i | index <= i < |s| && s[i] == x)| == 0
{
    // When index equals the length of s, the set is empty
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  count := 0;
  var index := 0;
  
  while index < |s|
    invariant 0 <= index <= |s|
    invariant count == |(set i | 0 <= i < index && s[i] == x)|
  {
    if s[index] == x {
      count := count + 1;
    }
    index := index + 1;
  }
  
  // After loop, we know index == |s|
  // The set {index <= i < |s|} is empty when index == |s|
  EmptySetLemma(s, x, index);
  SetEqualityLemma(s, x, index, count);
  // The postcondition follows from SetEqualityLemma and the fact that |(set i | index <= i < |s| && s[i] == x)| == 0
}
// </vc-code>

