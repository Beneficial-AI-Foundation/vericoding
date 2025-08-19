predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

//IMPL 
method CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  count := 0;
  var digitIndices: set<int> := {};
  
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant digitIndices == set j: int | 0 <= j < i && IsDigit(s[j])
    invariant count == |digitIndices|
  {
    if IsDigit(s[i]) {
      digitIndices := digitIndices + {i};
      count := count + 1;
    }
  }
  
  assert digitIndices == set i: int | 0 <= i < |s| && IsDigit(s[i]);
}