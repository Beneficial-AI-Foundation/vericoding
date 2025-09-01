

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
}
// </vc-code>

