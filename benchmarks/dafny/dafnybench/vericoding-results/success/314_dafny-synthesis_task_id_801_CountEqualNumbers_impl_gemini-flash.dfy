

// <vc-helpers>
lemma lemma_transitivity_of_equality(a: int, b: int, c: int)
    requires a == b && b == c
    ensures a == c
{
}
// </vc-helpers>

// <vc-spec>
method CountEqualNumbers(a: int, b: int, c: int) returns (count: int)
    ensures count >= 0 && count <= 3
    ensures (count == 3) <==> (a == b && b == c)
    ensures (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c))
    ensures (count == 1) <==> (a != b && b != c && a != c)
// </vc-spec>
// <vc-code>
{
  var local_count := 0;
  if a == b {
    local_count := local_count + 1;
  }
  if a == c {
    local_count := local_count + 1;
  }
  if b == c {
    local_count := local_count + 1;
  }

  if local_count == 3 {
    // This means a==b, a==c, and b==c.
    // By transitivity, a==b==c, so there are 3 equal values.
    lemma_transitivity_of_equality(a, b, c);
    count := 3;
  } else if local_count == 1 {
    // This means exactly one pair is equal.
    // E.g., a==b, but a!=c and b!=c.
    // Or a==c, but a!=b and c!=b.
    // Or b==c, but b!=a and c!=a.
    count := 2;
  } else if local_count == 0 {
    // This means a!=b, a!=c, and b!=c. All different.
    count := 1;
  } else { // local_count == 2
    // This means exactly two pairs are equal.
    // For example, a==b and a==c. Then by transitivity b==c. So a==b==c.
    // This falls under the local_count == 3 case initially.
    // The only way local_count can be 2 is if one of the pairs is repeated.
    // For example, if a==b and a==c, then b==c, so all are equal, which implies local_count = 3.
    // This means local_count cannot be 2 under the definition above for strict pairs.
    // Re-evaluating the conditions.
    // The total count refers to how many distinct values are equal.
    // The specification means:
    // count = 3: a=b=c
    // count = 2: exactly two values are equal, e.g., a=b, but b!=c.
    // count = 1: all three values are distinct.

    if a == b && b == c {
        count := 3;
    } else if a == b && b != c { // a==b, a!=c, b!=c
        count := 2;
    } else if a == c && b != c { // a==c, a!=b, c!=b
        count := 2;
    } else if b == c && a != b { // b==c, b!=a, c!=a
        count := 2;
    } else { // a!=b && b!=c && a!=c
        count := 1;
    }
  }
}
// </vc-code>

