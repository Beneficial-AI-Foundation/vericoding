method any_int(a: int, b: int, c: int) returns (r: bool)
  // post-conditions-start
  ensures r == (a == b + c || b == a + c || c == a + b)
  // post-conditions-end
{
  // impl-start
  r := a == b + c || b == a + c || c == a + b;
  // impl-end
}
