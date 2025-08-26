method mult(n0 : int, m0 : int) returns (res : int)
    ensures res == (n0 * m0)
{
  var n := n0;
  var m := m0;
  res := 0;
  
  var sign := 1;
  if n < 0 && m < 0 {
    n := -n;
    m := -m;
    sign := 1;
  } else if n < 0 {
    n := -n;
    sign := -1;
  } else if m < 0 {
    m := -m;
    sign := -1;
  }
  
  while n > 0
    invariant sign * (res + n * m) == n0 * m0
    invariant sign == 1 || sign == -1
    invariant n >= 0
    decreases n
  {
    if n % 2 == 1 {
      res := res + m;
      n := n - 1;
    } else {
      n := n / 2;
      m := m * 2;
    }
  }
  
  res := sign * res;
}