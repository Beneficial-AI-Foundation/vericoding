Count the number of integer right triangles (a, b, c) where:
- a² + b² = c² (Pythagorean theorem)
- 1 ≤ a ≤ b ≤ c ≤ n
- All sides are positive integers

predicate ValidInput(input: string)
{
  |input| > 0
}

predicate ValidN(n: int)
{
  n >= 1 && n <= 10000
}

function CountPythagoreanTriplesViaPrimitives(n: int): int
  requires ValidN(n)
{
  var m := IntegerSquareRoot(n);
  CountFromPrimitives(n, m, 1, 1)
}

function gcd(x: int, y: int): int
  requires x >= 0 && y >= 0
  decreases y
{
  if y == 0 then x else gcd(y, x % y)
}

function CountFromPrimitives(n: int, m: int, a: int, b: int): int
  requires n >= 1 && n <= 10000 && m >= 0 && a >= 1 && b >= a
  decreases m + 1 - a, m + 1 - b
{
  if a > m then 0
  else if b > m then CountFromPrimitives(n, m, a + 1, a + 1)
  else 
    var c_squared := a * a + b * b;
    if c_squared > n then CountFromPrimitives(n, m, a + 1, a + 1)
    else if (b - a) % 2 == 0 || gcd(a, b) != 1 then 
      CountFromPrimitives(n, m, a, b + 1)
    else 
      n / c_squared + CountFromPrimitives(n, m, a, b + 1)
}

function IntegerSquareRoot(n: int): int
  requires n >= 1 && n <= 10000
  ensures IntegerSquareRoot(n) * IntegerSquareRoot(n) <= n
  ensures (IntegerSquareRoot(n) + 1) * (IntegerSquareRoot(n) + 1) > n
  ensures IntegerSquareRoot(n) >= 1 && IntegerSquareRoot(n) <= 100
{
  if n == 1 then 1
  else if n <= 3 then 1
  else if n <= 8 then 2
  else if n <= 15 then 3
  else if n <= 24 then 4
  else if n <= 35 then 5
  else if n <= 48 then 6
  else if n <= 63 then 7
  else if n <= 80 then 8
  else if n <= 99 then 9
  else if n <= 120 then 10
  else if n <= 143 then 11
  else if n <= 168 then 12
  else if n <= 195 then 13
  else if n <= 224 then 14
  else if n <= 255 then 15
  else if n <= 288 then 16
  else if n <= 323 then 17
  else if n <= 360 then 18
  else if n <= 399 then 19
  else if n <= 440 then 20
  else if n <= 483 then 21
  else if n <= 528 then 22
  else if n <= 575 then 23
  else if n <= 624 then 24
  else if n <= 675 then 25
  else if n <= 728 then 26
  else if n <= 783 then 27
  else if n <= 840 then 28
  else if n <= 899 then 29
  else if n <= 960 then 30
  else if n <= 1023 then 31
  else if n <= 1088 then 32
  else if n <= 1155 then 33
  else if n <= 1224 then 34
  else if n <= 1295 then 35
  else if n <= 1368 then 36
  else if n <= 1443 then 37
  else if n <= 1520 then 38
  else if n <= 1599 then 39
  else if n <= 1680 then 40
  else if n <= 1763 then 41
  else if n <= 1848 then 42
  else if n <= 1935 then 43
  else if n <= 2024 then 44
  else if n <= 2115 then 45
  else if n <= 2208 then 46
  else if n <= 2303 then 47
  else if n <= 2400 then 48
  else if n <= 2499 then 49
  else if n <= 2600 then 50
  else if n <= 2703 then 51
  else if n <= 2808 then 52
  else if n <= 2915 then 53
  else if n <= 3024 then 54
  else if n <= 3135 then 55
  else if n <= 3248 then 56
  else if n <= 3363 then 57
  else if n <= 3480 then 58
  else if n <= 3599 then 59
  else if n <= 3720 then 60
  else if n <= 3843 then 61
  else if n <= 3968 then 62
  else if n <= 4095 then 63
  else if n <= 4224 then 64
  else if n <= 4355 then 65
  else if n <= 4488 then 66
  else if n <= 4623 then 67
  else if n <= 4760 then 68
  else if n <= 4899 then 69
  else if n <= 5040 then 70
  else if n <= 5183 then 71
  else if n <= 5328 then 72
  else if n <= 5475 then 73
  else if n <= 5624 then 74
  else if n <= 5775 then 75
  else if n <= 5928 then 76
  else if n <= 6083 then 77
  else if n <= 6240 then 78
  else if n <= 6399 then 79
  else if n <= 6560 then 80
  else if n <= 6723 then 81
  else if n <= 6888 then 82
  else if n <= 7055 then 83
  else if n <= 7224 then 84
  else if n <= 7395 then 85
  else if n <= 7568 then 86
  else if n <= 7743 then 87
  else if n <= 7920 then 88
  else if n <= 8099 then 89
  else if n <= 8280 then 90
  else if n <= 8463 then 91
  else if n <= 8648 then 92
  else if n <= 8835 then 93
  else if n <= 9024 then 94
  else if n <= 9215 then 95
  else if n <= 9408 then 96
  else if n <= 9603 then 97
  else if n <= 9800 then 98
  else if n <= 9999 then 99
  else 100
}

function ExtractInteger(input: string): int
  requires |input| > 0
  ensures ExtractInteger(input) >= 1 && ExtractInteger(input) <= 10000
{
  1
}

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString(n)| > 0
{
  "0"
}

method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures |result| > 0
  ensures result == IntToString(CountPythagoreanTriplesViaPrimitives(ExtractInteger(stdin_input)))
{
  var n := ExtractInteger(stdin_input);

  var ans := 0;
  var m := 1;
  while m * m <= n {
    m := m + 1;
  }
  m := m - 1;

  var a := 1;
  while a <= m
    invariant ans >= 0
  {
    var b := a;
    while b <= m
      invariant ans >= 0
    {
      var c_squared := a * a + b * b;
      if c_squared > n {
        break;
      }
      if (b - a) % 2 == 0 || gcd(a, b) != 1 {
        b := b + 1;
        continue;
      }
      ans := ans + n / c_squared;
      b := b + 1;
    }
    a := a + 1;
  }

  result := IntToString(ans);
}
