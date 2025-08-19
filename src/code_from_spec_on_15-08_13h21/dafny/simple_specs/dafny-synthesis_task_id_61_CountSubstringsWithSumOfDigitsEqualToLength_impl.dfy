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
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
  {
    var j := i;
    var digitSum := 0;
    
    while j < |s|
      invariant i <= j <= |s|
      invariant digitSum >= 0
      invariant count >= 0
    {
      if IsDigit(s[j]) {
        digitSum := digitSum + (s[j] as int - 48);
      }
      
      var substringLength := j - i + 1;
      if digitSum == substringLength {
        count := count + 1;
      }
      
      j := j + 1;
    }
    
    i := i + 1;
  }
}