//ATOM
predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

//IMPL
method CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant count == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
  {
    if IsUpperCase(s[i]) {
      count := count + 1;
      /* code modified by LLM (iteration 2): Added lemma call to prove set cardinality when adding uppercase character */
      UppercaseCardinalityLemma(s, i);
    } else {
      /* code modified by LLM (iteration 2): Added lemma call to prove set cardinality remains same when character is not uppercase */
      NonUppercaseCardinalityLemma(s, i);
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 2): Helper lemma for when character is uppercase */
lemma UppercaseCardinalityLemma(s: string, i: int)
  requires 0 <= i < |s|
  requires IsUpperCase(s[i])
  ensures | set j: int | 0 <= j < i + 1 && IsUpperCase(s[j])| == | set j: int | 0 <= j < i && IsUpperCase(s[j])| + 1
{
  var before := set j: int | 0 <= j < i && IsUpperCase(s[j]);
  var after := set j: int | 0 <= j < i + 1 && IsUpperCase(s[j]);
  
  assert after == before + {i};
  assert i !in before;
}

/* code modified by LLM (iteration 2): Helper lemma for when character is not uppercase */
lemma NonUppercaseCardinalityLemma(s: string, i: int)
  requires 0 <= i < |s|
  requires !IsUpperCase(s[i])
  ensures | set j: int | 0 <= j < i + 1 && IsUpperCase(s[j])| == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
{
  var before := set j: int | 0 <= j < i && IsUpperCase(s[j]);
  var after := set j: int | 0 <= j < i + 1 && IsUpperCase(s[j]);
  
  assert after == before;
}