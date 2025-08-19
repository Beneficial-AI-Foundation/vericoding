//ATOM
predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

//IMPL CountDigits
method CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant count == | set j: int | 0 <= j < i && IsDigit(s[j])|
  {
    if IsDigit(s[i]) {
      /* code modified by LLM (iteration 3): Direct assertion about set cardinality without helper lemma */
      assert i !in (set j: int | 0 <= j < i && IsDigit(s[j]));
      assert (set j: int | 0 <= j < i+1 && IsDigit(s[j])) == (set j: int | 0 <= j < i && IsDigit(s[j])) + {i};
      count := count + 1;
    } else {
      /* code modified by LLM (iteration 3): Assert set equality when no digit is added */
      assert (set j: int | 0 <= j < i+1 && IsDigit(s[j])) == (set j: int | 0 <= j < i && IsDigit(s[j]));
    }
    i := i + 1;
  }
}