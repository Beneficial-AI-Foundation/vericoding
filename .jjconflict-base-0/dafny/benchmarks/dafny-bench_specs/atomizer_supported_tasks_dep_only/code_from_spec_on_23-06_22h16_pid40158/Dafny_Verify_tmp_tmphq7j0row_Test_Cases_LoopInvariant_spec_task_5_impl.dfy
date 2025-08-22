//ATOM UpWhileLess
method UpWhileLess(n: int) returns (i: int)
  ensures i >= n
{
  i := 0;
  while i < n
    invariant i <= n
  {
    i := i + 1;
  }
}

//ATOM UpWhileNotEqual
method UpWhileNotEqual(n: int) returns (i: int)
  requires n >= 0
  ensures i == n
{
  i := 0;
  while i != n
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
}

//ATOM DownWhileNotEqual
method DownWhileNotEqual(n: int) returns (i: int)
  requires n >= 0
  ensures i == 0
{
  i := n;
  while i != 0
    invariant 0 <= i <= n
  {
    i := i - 1;
  }
}

//ATOM DownWhileGreater
method DownWhileGreater(n: int) returns (i: int)
  ensures i <= n
{
  i := n + 10; // start with some value greater than n
  while i > n
    invariant i >= n
  {
    i := i - 1;
  }
}

//IMPL Quotient
method Quotient(a: int, b: int) returns (q: int, r: int)
  requires b > 0
  ensures a == q * b + r && 0 <= r < b
{
  /* code modified by LLM (iteration 2): handle non-negative case with proper invariant */
  if a >= 0 {
    q := 0;
    r := a;
    while r >= b
      invariant a == q * b + r && r >= 0
      decreases r
    {
      r := r - b;
      q := q + 1;
    }
  } else {
    /* code modified by LLM (iteration 2): handle negative case by computing floor division */
    var temp_q := 0;
    var temp_r := -a;
    
    while temp_r >= b
      invariant -a == temp_q * b + temp_r && temp_r >= 0
      decreases temp_r
    {
      temp_r := temp_r - b;
      temp_q := temp_q + 1;
    }
    
    /* code modified by LLM (iteration 2): adjust quotient and remainder for negative dividend */
    if temp_r == 0 {
      q := -temp_q;
      r := 0;
    } else {
      q := -(temp_q + 1);
      r := b - temp_r;
    }
  }
}