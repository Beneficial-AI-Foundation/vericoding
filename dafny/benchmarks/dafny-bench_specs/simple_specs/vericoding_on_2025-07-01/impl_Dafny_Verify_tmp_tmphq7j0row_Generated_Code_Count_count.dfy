The `has_count` function recursively counts occurrences of value `v` in the first `n` elements of array `a`. To implement the `count` method, I need to create an iterative version that produces the same result.

I'll use a loop that iterates through the array elements from index 0 to n-1, incrementing a counter whenever I find the target value `v`.

//ATOM
function has_count(v: int, a: array<int>, n: int): int
  reads a // This allows the function to read from array 'a'
  requires n >= 0 && n <= a.Length
{
  if n == 0 then 0 else
  (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}

//IMPL
method count (v: int, a: array<int>, n: int) returns (r: int)
  requires n >= 0 && n <= a.Length
  ensures has_count(v, a, n) == r
{
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == has_count(v, a, i)
  {
    if a[i] == v {
      r := r + 1;
    }
    i := i + 1;
  }
}