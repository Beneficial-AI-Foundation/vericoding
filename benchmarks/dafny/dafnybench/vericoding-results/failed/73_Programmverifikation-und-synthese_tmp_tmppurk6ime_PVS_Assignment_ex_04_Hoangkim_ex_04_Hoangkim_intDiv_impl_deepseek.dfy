//Problem 01

//problem02
//a)

// <vc-helpers>
lemma LemmaDiv(n: int, d: int) 
  requires d > 0
  ensures exists q: int, r: int :: d * q + r == n && 0 <= r < d
{
  if n < 0 {
    var q' := n / d - 1;
    var r' := n - d * q';
    assert d * q' + r' == n;
    assert 0 <= r' < d;
  } else {
    var q' := n / d;
    var r' := n % d;
    assert d * q' + r' == n;
    assert 0 <= r' < d;
  }
}

lemma LemmaDivBound(n: int, d: int)
  requires n >= 0 && d > 0
  ensures n / d <= n
{
  // Since d >= 1, n/d <= n
}

lemma LemmaDivQuotientBound(n: int, d: int)
  requires n >= d && n >= 0 && d > 0
  ensures n / d <= n
{
}

lemma LemmaDivHalfBound(n: int, d: int)
  requires n >= d && n >= 0 && d > 0
  ensures n / d <= n / 2 | n / d > n / 2
{
}
// </vc-helpers>

// <vc-spec>
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
// </vc-spec>
// <vc-code>
{
  var temp_q := n / d;
  var temp_r := n % d;
  
  q := temp_q;
  r := temp_r;
  
  if q > n / 2 {
    var decrease_amount := (q - n / 2) + 1;
    q := q - decrease_amount;
    r := r + d * decrease_amount;
    
    while r >= d
      decreases r - d
    {
      q := q + 1;
      r := r - d;
    }
  }
  
  assert d * q + r == n;
  assert 0 <= r < d;
  assert 0 <= q <= n / 2;
}
// </vc-code>

