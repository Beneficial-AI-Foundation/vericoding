predicate ValidInput(lines: seq<string>)
{
    |lines| > 0
}

function MAX_VALUE(): int { 4294967295 }

predicate IsOverflow(x: int)
{
    x > MAX_VALUE()
}

// <vc-helpers>
method Parse(s: string) returns (val: int, is_overflow: bool)
  ensures !is_overflow ==> val >= 0 && !IsOverflow(val)
{
  val := 0;
  is_overflow := false;
  var i := 0;
  while i < |s| && !is_overflow
    invariant 0 <= i <= |s|
    invariant !is_overflow ==> val >= 0 && !IsOverflow(val)
    decreases |s| - i
  {
    var c := s[i];
    if '0' <= c <= '9' {
      var digit := c as int - '0' as int;
      if val > (MAX_VALUE() - digit) / 10 {
        is_overflow := true;
      } else {
        val := val * 10 + digit;
      }
    } else {
      is_overflow := true;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput([input])
    ensures result == "OVERFLOW!!!" || result != "OVERFLOW!!!"
// </vc-spec>
// <vc-code>
{
  var val, is_overflow := Parse(input);
  if is_overflow {
    result := "OVERFLOW!!!";
  } else {
    result := "OK";
  }
}
// </vc-code>

