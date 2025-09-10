predicate ValidInput(n: int, a: seq<int>, k: string)
{
  n >= 1 && |a| == n && |k| == n && 
  (forall i :: 0 <= i < n ==> a[i] >= 0) &&
  isBinaryString(k)
}

predicate isBinaryString(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function binaryStringToInt(s: string): int
  requires isBinaryString(s)
  ensures binaryStringToInt(s) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == '1' then 1 else 0) * pow(2, |s|-1) + binaryStringToInt(s[1..])
}

function f(a: seq<int>, x: int, n: int): int
  requires n >= 0
  requires |a| == n
  ensures (forall i :: 0 <= i < n ==> a[i] >= 0) ==> f(a, x, n) >= 0
{
  if n == 0 then 0
  else (if (x / pow(2, n-1)) % 2 == 1 then a[n-1] else 0) + f(a[..n-1], x % pow(2, n-1), n-1)
}

// <vc-helpers>
function pow(b: int, e: int): int
  requires e >= 0
  decreases e
  ensures b >= 0 ==> pow(b,e) >= 0
  ensures b > 0 && e >= 0 ==> pow(b,e) > 0
{
  if e == 0 then 1 else b * pow(b, e - 1)
}

lemma pow_pos(b: int, e: int)
  requires e >= 0
  requires b > 0
  ensures pow(b, e) > 0
  decreases e
{
  if e == 0 {
  } else {
    pow_pos(b, e - 1);
  }
}

lemma f_zero(a: seq<int>, n: int)
  requires n >= 0
  requires |a| == n
  ensures f(a, 0, n) == 0
  decreases n
{
  if n == 0 {
  } else {
    assert n - 1 >= 0;
    // pow(2, n-1) > 0
    assert pow(2, n-1) > 0;
    // 0 / m == 0 for m > 0
    assert 0 / pow(2, n-1) == 0;
    assert (0 / pow(2, n-1)) % 2 == 0;
    f_zero(a[..n-1], n-1);
    assert f(a[..n-1], 0 % pow(2, n-1), n-1) == 0;
    assert f(a, 0, n) == 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, k: string) returns (result: int)
  requires ValidInput(n, a, k)
  ensures result >= 0
  ensures exists x :: 0 <= x <= binaryStringToInt(k) && result == f(a, x, n)
  ensures forall x :: 0 <= x <= binaryStringToInt(k) ==> f(a, x, n) <= result
// </vc-spec>
// <vc-code>
{
  var kVal := binaryStringToInt(k);
  result := 0;
  var i := 0;
  f_zero(a, n);
  while i <= kVal
    invariant 0 <= i <= kVal + 1
    invariant forall y :: 0 <= y < i ==> f(a, y, n) <= result
    invariant exists y :: 0 <= y <= kVal && result == f(a, y, n)
    decreases kVal - i
  {
    var cur := f(a, i, n);
    if cur > result {
      result := cur;
    }
    i := i + 1;
  }
}
// </vc-code>

