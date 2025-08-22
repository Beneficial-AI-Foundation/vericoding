//ATOM


// Ghost
ghost function Double(val:int) : int
{
  2 * val
}


//IMPL TestDouble

method TestDouble(val: int) returns (val2:int)
  ensures val2 == Double(val)
{
  val2 := 2 * val;
}