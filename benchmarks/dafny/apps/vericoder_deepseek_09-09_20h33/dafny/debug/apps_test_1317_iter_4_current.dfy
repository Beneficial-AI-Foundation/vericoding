function CountCellsDivisibleByM(n: int, m: int): int
  requires 1 <= n
  requires 1 <= m
{
  |set i, j | 1 <= i <= n && 1 <= j <= n && (i * i + j * j) % m == 0 :: (i, j)|
}

predicate ValidInput(n: int, m: int) {
  1 <= n && 1 <= m <= 1000
}

// <vc-helpers>
lemma CountDivisible(n: int, m: int, k: int, count: int)
  requires 1 <= n && 1 <= m <= 1000
  requires 0 <= k <= n
  requires count == (|set i, j | 1 <= i <= k && 1 <= j <= n && (i * i + j * j) % m == 0 :: (i, j)|)
  ensures count <= CountCellsDivisibleByM(n, m)
  decreases n - k
{
  if k < n {
    var next := k + 1;
    var additional := (|set j | 1 <= j <= n && (next * next + j * j) % m == 0 :: j|);
    CountDivisible(n, m, next, count + additional);
  }
}

lemma SquaredModProperties(i: int, j: int, m: int)
  requires 1 <= m <= 1000
  ensures (i * i + j * j) % m == ((i % m) * (i % m) + (j % m) * (j % m)) % m
{
  var a := i % m;
  var b := j % m;
  calc {
    (i * i + j * j) % m;
    == { ModSum(i * i, j * j, m); }
    ((i * i) % m + (j * j) % m) % m;
    == { ModProduct(i, i, m); ModProduct(j, j, m); }
    (((i % m) * (i % m)) % m + ((j % m) * (j % m)) % m) % m;
    == { ModSum((i % m) * (i % m), (j % m) * (j % m), m); }
    ((i % m) * (i % m) + (j % m) * (j % m)) % m;
  }
}

lemma ModProduct(a: int, b: int, m: int)
  requires m != 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  calc {
    (a * b) % m;
    == { assert a * b == ((a % m) + (a / m) * m) * ((b % m) + (b / m) * m); }
    ((a % m) * (b % m) + m * K) % m for some K;
    == 
    ((a % m) * (b % m)) % m;
  }
}

lemma ModSum(a: int, b: int, m: int)
  requires m != 0
  ensures (a + b) % m == ((a % m) + (b % m)) % m
{
  calc {
    (a + b) % m;
    == { assert a + b == (a % m) + (b % m) + m * ((a / m) + (b / m)); }
    ((a % m) + (b % m)) % m;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= 0
  ensures result == CountCellsDivisibleByM(n, m)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == (|set x, y | 1 <= x < i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|)
    decreases n + 1 - i
  {
    var row_count := 0;
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant row_count == (|set y | 1 <= y < j && (i * i + y * y) % m == 0 :: y|)
      decreases n + 1 - j
    {
      if (i * i + j * j) % m == 0 {
        row_count := row_count + 1;
      }
      j := j + 1;
    }
    result := result + row_count;
    i := i + 1;
  }
  CountDivisible(n, m, n, result);
  assert i == n + 1;
}
// </vc-code>

