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
      /* code modified by LLM (iteration 2): Fixed assertion syntax to properly compare sets */
      assert (set j: int | 0 <= j < i+1 && IsUpperCase(s[j])) == (set j: int | 0 <= j < i && IsUpperCase(s[j])) + {i};
    } else {
      /* code modified by LLM (iteration 2): Fixed assertion syntax for the non-uppercase case */
      assert (set j: int | 0 <= j < i+1 && IsUpperCase(s[j])) == (set j: int | 0 <= j < i && IsUpperCase(s[j]));
    }
    i := i + 1;
  }
}