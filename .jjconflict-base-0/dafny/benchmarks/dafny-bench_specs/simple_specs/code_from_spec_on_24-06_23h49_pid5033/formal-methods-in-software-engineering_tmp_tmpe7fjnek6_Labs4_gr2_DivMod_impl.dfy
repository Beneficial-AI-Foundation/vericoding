//IMPL DivMod
method DivMod(a: int, b: int) returns (q: int, r: int)
  requires b != 0
  ensures a == b * q + r
  ensures 0 <= r < (if b > 0 then b else -b)
{
  if a >= 0 && b > 0 {
    q := a / b;
    r := a % b;
  } else if a >= 0 && b < 0 {
    q := -(a / (-b));
    r := a % (-b);
  } else if a < 0 && b > 0 {
    var pos_a := -a;
    var temp_q := pos_a / b;
    var temp_r := pos_a % b;
    if temp_r == 0 {
      q := -temp_q;
      r := 0;
    } else {
      q := -(temp_q + 1);
      r := b - temp_r;
    }
  } else { // a < 0 && b < 0
    var pos_a := -a;
    var pos_b := -b;
    var temp_q := pos_a / pos_b;
    var temp_r := pos_a % pos_b;
    if temp_r == 0 {
      q := temp_q;
      r := 0;
    } else {
      q := temp_q + 1;
      r := pos_b - temp_r;
    }
  }
}