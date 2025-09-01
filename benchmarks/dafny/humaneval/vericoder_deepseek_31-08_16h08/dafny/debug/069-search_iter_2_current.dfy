

// <vc-helpers>
lemma CountLemma(s: seq<int>, x: int, count: int)
    requires 0 <= count <= |s|
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)| <==>
        (forall i :: 0 <= i < |s| ==> (s[i] == x) == (i < count))
{
    // This lemma helps establish the connection between the count and the set
    if count == |(set i | 0 <= i < |s| && s[i] == x)| {
        // If counts match, then the first 'count' elements are all 'x'
        // and the remaining elements are not 'x'
    } else {
        // If counts don't match, there must be an inconsistency
    }
}

lemma SetEqualityLemma(s: seq<int>, x: int, index: int, count: int)
    requires 0 <= index <= |s|
    requires count == |(set i | 0 <= i < index && s[i] == x)|
    ensures |(set i | 0 <= i < |s| && s[i] == x)| == count + |(set i | index <= i < |s| && s[i] == x)|
{
}
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
  // Use lemma to connect the loop invariant to the postcondition
  SetEqualityLemma(s, x, index, count);
}
// </vc-code>

