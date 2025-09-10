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
{
}

lemma SquaredModProperties(i: int, j: int, m: int)
  requires 1 <= m <= 1000
  ensures (i * i + j * j) % m == ((i % m) * (i % m) + (j % m) * (j % m)) % m
{
  var a := i % m;
  var b := j % m;
  assert (i * i) % m == (a * a) % m by {
    calc {
      (i * i) % m;
      == { ModProduct(i, i, m); }
      ((i % m) * (i % m)) % m;
      == { }
      (a * a) % m;
    }
  }
  assert (j * j) % m == (b * b) % m by {
    calc {
      (j * j) % m;
      == { ModProduct(j, j, m); }
      ((j % m) * (j % m)) % m;
      == { }
      (b * b) % m;
    }
  }
  calc {
    (i * i + j * j) % m;
    == { ModSum(i*i, j*j, m); }
    ((i * i) % m + (j * j) % m) % m;
    == { }
    ((a * a) % m + (b * b) % m) % m;
    == { ModSum(a*a, b*b, m); }
    (a * a + b * b) % m;
    == { }
    ((i % m) * (i % m) + (j % m) * (j % m)) % m;
  }
}

lemma ModProduct(a: int, b: int, m: int)
  requires m != 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma ModSum(a: int, b: int, m: int)
  requires m != 0
  ensures (a + b) % m == ((a % m) + (b % m)) % m
{
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
  {
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant result == (|set x, y | 1 <= x < i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|) +
                         (|set y | 1 <= y < j && (i * i + y * y) % m == 0 :: (i, y)|)
    {
      if (i * i + j * j) % m == 0 {
        result := result + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert i == n + 1;
  assert result == (|set x, y | 1 <= x < n + 1 && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|);
  assert CountCellsDivisibleByM(n, m) == (|set x, y | 1 <= x <= n && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|);
}
// </vc-code>

