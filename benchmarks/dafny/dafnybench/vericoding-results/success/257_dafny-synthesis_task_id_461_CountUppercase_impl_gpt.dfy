predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

// <vc-helpers>
lemma Cardinality_AddOne(S: set<int>, x: int)
    requires x !in S
    ensures |S + {x}| == |S| + 1
{
}
// </vc-helpers>

// <vc-spec>
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// </vc-spec>
// <vc-code>
{
  var i := 0;
  count := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant count == | set j: int | 0 <= j < i && IsUpperCase(s[j]) |
    decreases |s| - i
  {
    if IsUpperCase(s[i]) {
      assert i !in (set j: int | 0 <= j < i && IsUpperCase(s[j]));
      assert (set j: int | 0 <= j < i + 1 && IsUpperCase(s[j])) ==
             (set j: int | 0 <= j < i && IsUpperCase(s[j])) + {i};
      Cardinality_AddOne((set j: int | 0 <= j < i && IsUpperCase(s[j])), i);
      count := count + 1;
    } else {
      assert (set j: int | 0 <= j < i + 1 && IsUpperCase(s[j])) ==
             (set j: int | 0 <= j < i && IsUpperCase(s[j]));
    }
    i := i + 1;
  }
}
// </vc-code>

