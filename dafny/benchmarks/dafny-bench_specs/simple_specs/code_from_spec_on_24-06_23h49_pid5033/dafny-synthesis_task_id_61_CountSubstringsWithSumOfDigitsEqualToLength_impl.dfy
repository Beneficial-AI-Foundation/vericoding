//ATOM
predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

//IMPL
method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
  ensures count >= 0
{
  count := 0;
  var n := |s|;
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count >= 0
  {
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant count >= 0
    {
      var substring := s[i..j+1];
      var digitSum := 0;
      var k := 0;
      while k < |substring|
        invariant 0 <= k <= |substring|
        invariant digitSum >= 0
      {
        if IsDigit(substring[k]) {
          digitSum := digitSum + (substring[k] as int - 48);
        }
        k := k + 1;
      }
      
      if digitSum == |substring| {
        count := count + 1;
      }
      
      j := j + 1;
    }
    i := i + 1;
  }
}