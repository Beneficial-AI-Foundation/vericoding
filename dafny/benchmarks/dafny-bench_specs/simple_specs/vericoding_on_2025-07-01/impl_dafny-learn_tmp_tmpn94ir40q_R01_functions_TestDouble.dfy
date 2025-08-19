//ATOM

// Ghost
ghost function Double(val:int) : int
{
  2 * val
}


// SPEC

method TestDouble(val: int) returns (val2:int)
  ensures val2 == Double(val)
{
}