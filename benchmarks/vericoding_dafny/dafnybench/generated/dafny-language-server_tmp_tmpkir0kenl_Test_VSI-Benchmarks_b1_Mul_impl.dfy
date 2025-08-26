method Add(x: int, y: int) returns (r: int)
  ensures r == x+y;
{
  r := x;
  if (y < 0) {
    var n := y;
    while (n != 0)
      invariant r == x+y-n && 0 <= -n;
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while (n != 0)
      invariant r == x+y-n && 0 <= n;
    {
      r := r + 1;
      n := n - 1;
    }
  }
}

// <vc-helpers>
// </vc-helpers>

method Mul(x: int, y: int) returns (r: int)
  ensures r == x*y;
  decreases if x < 0 then -x else x;
// </vc-spec>
// <vc-code>
{
  if (x == 0) {
    r := 0;
  } else if (x > 0) {
    var temp := Mul(x - 1, y);
    r := Add(temp, y);
  } else {
    var temp := Mul(x + 1, y);
    r := Add(temp, -y);
  }
}
// </vc-code>

// ---------------------------