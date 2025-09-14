// <vc-preamble>
predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): corrected lemma signature and provided proof */
lemma CardinalityOfUppercaseSet(s: string, i: int)
    requires 0 <= i < |s|
    ensures |set j | 0 <= j < i + 1 && IsUpperCase(s[j])| ==
        (|set j | 0 <= j < i && IsUpperCase(s[j])|) + (if IsUpperCase(s[i]) then 1 else 0)
{
    assert (set j | 0 <= j < i + 1 && IsUpperCase(s[j])) ==
           (set j | 0 <= j < i && IsUpperCase(s[j])) +
           (if IsUpperCase(s[i]) then {i} else {});
}
// </vc-helpers>

// <vc-spec>
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added call to helper lemma to prove loop invariant */
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |set j: int | 0 <= j < i && IsUpperCase(s[j])|
  {
    CardinalityOfUppercaseSet(s, i);
    if IsUpperCase(s[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
