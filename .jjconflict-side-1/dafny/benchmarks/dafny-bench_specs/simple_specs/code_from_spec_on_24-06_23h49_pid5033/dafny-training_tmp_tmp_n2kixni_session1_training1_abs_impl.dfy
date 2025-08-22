//IMPL 
method abs(x: int) returns (y: int)
  ensures true
{
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

/** Call abs */