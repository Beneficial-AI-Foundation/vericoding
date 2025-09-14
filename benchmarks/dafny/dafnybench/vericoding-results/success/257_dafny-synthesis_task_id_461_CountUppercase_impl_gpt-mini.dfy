predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

// <vc-helpers>
lemma CountStep(s: string, i: int)
  requires 0 <= i < |s|
  ensures | set j: int | 0 <= j < i+1 && IsUpperCase(s[j]) | ==
          | set j: int | 0 <= j < i && IsUpperCase(s[j]) | + (if IsUpperCase(s[i]) then 1 else 0)
{
  var A := set j: int | 0 <= j < i && IsUpperCase(s[j]);
  var B := set j: int | 0 <= j < i+1 && IsUpperCase(s[j]);
  if IsUpperCase(s[i]) {
    // i is not in A because every element of A is strictly less than i
    assert forall k :: k in A ==> k < i;
    assert i !in A;
    // show B = A ∪ {i}
    assert forall x :: x in B <==> (x in A || x == i);
    assert B == A + {i};
    // cardinality of A ∪ {i} is |A| + 1 because i ∉ A
    assert |B| == |A + {i}|;
    assert |A + {i}| == |A| + 1;
  } else {
    // if s[i] is not uppercase then B = A
    assert forall x :: x in B <==> x in A;
    assert B == A;
  }
}
// </vc-helpers>

// <vc-spec>
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
  {
    var old_i := i;
    if IsUpperCase(s[old_i]) {
      count := count + 1;
    }
    CountStep(s, old_i);
    assert count == | set j: int | 0 <= j < old_i+1 && IsUpperCase(s[j]) |;
    i := old_i + 1;
    assert count == | set j: int | 0 <= j < i && IsUpperCase(s[j]) |;
  }
}
// </vc-code>

