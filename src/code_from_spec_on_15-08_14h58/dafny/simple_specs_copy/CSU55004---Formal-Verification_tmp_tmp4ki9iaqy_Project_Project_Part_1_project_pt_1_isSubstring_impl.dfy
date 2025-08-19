//ATOM
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  res := false;
  return res;
}

//IMPL 
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
  requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
  res := false;
  var i := 0;
  while i <= |str| - |sub|
  {
    var suffix := str[i..];
    var prefixResult := isPrefix(sub, suffix);
    if prefixResult {
      res := true;
      return;
    }
    i := i + 1;
  }
}