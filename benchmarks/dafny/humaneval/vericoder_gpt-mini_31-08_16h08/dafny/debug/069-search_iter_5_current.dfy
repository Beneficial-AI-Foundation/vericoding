

// <vc-helpers>
function CountPrefix(s: seq<int>, x: int, i: int): int
  requires 0 <= i <= |s|
  decreases i
{
  if i == 0 then 0 else CountPrefix(s, x, i-1) + (if s[i-1] == x then 1 else 0)
}

lemma CountPrefixExtend(s: seq<int>, x: int, i: int)
  requires 0 <= i < |s|
  ensures CountPrefix(s, x, i+1) == CountPrefix(s, x, i) + (if s[i] == x then 1 else 0)
{
  // Follows directly from the definition of CountPrefix
}

lemma CountPrefixEqSet(s: seq<int>, x: int, i: int)
  requires 0 <= i <= |s|
  ensures CountPrefix(s, x, i) == |(set j | 0 <= j < i && s[j] == x)|
{
  if i == 0 {
    // both sides are 0
  } else {
    // Inductive hypothesis
    CountPrefixEqSet(s, x, i-1);
    // Unfold definition
    assert CountPrefix(s, x, i) == CountPrefix(s, x, i-1) + (if s[i-1] == x then 1 else 0);

    // Show the corresponding equality for the set cardinality:
    // The set for i is the union of the set for i-1 and possibly {i-1}, and i-1 is not in the former set.
    assert forall k :: (k in (set j | 0 <= j < i && s[j] == x)) <==>
                       ((k in (set j | 0 <= j < i-1 && s[j] == x)) || (k == i-1 && s[i-1] == x))
      by {
        // Proof of membership equivalence by cases on k
        var k := 0;
        // This is a quantifier proof; body not needed for verifier with these facts.
      };

    // From the membership equivalence and disjointness of i-1 from the earlier set,
    // the cardinalities differ by exactly (if s[i-1]==x then 1 else 0).
    assert |(set j | 0 <= j < i && s[j] == x)| ==
           |(set j | 0 <= j < i-1 && s[j] == x)| + (if s[i-1] == x then 1 else 0);

    // Combine equalities using the inductive hypothesis
    assert CountPrefix(s, x, i) == |(set j | 0 <= j < i && s[j] == x)|
      by {
        // CountPrefix(s,x,i-1) == |set ... i-1 ...| by inductive hypothesis
      };
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
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == CountPrefix(s, x, i)
    decreases |s| - i
  {
    if s[i] == x {
      count := count + 1;
    }
    // Help the verifier relate CountPrefix at i and i+1
    CountPrefixExtend(s, x, i);
    i := i + 1;
  }
  // Relate CountPrefix at full length to the set cardinality required by the postcondition
  CountPrefixEqSet(s, x, |s|);
  assert count == |(set j | 0 <= j < |s| && s[j] == x)|;
}
// </vc-code>

