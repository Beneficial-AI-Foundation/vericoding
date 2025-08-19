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
    /* code modified by LLM (iteration 2): fixed type errors by working with index sets correctly */
    var old_set := set j: int | 0 <= j < i && IsUpperCase(s[j]);
    var new_set := set j: int | 0 <= j < i + 1 && IsUpperCase(s[j]);
    
    if IsUpperCase(s[i]) {
      assert i in new_set;
      assert new_set == old_set + {i};
      assert i !in old_set ==> |new_set| == |old_set| + 1;
      count := count + 1;
    } else {
      assert i !in new_set;
      assert new_set == old_set;
      assert |new_set| == |old_set|;
    }
    
    i := i + 1;
    
    assert count == |set j: int | 0 <= j < i && IsUpperCase(s[j])|;
  }
}