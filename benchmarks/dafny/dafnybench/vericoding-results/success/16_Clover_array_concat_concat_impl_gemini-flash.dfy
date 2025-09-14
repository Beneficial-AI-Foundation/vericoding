

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method concat(a:array<int>, b:array<int>) returns (c:array<int>)
  ensures c.Length==b.Length+a.Length
  ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k :: 0 <= k < b.Length ==> c[k+a.Length] == b[k]
// </vc-spec>
// <vc-code>
{
  var c_arr := new int[a.Length + b.Length];

  // Copy elements from array 'a' to 'c_arr'
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> c_arr[k] == a[k]
    invariant c_arr.Length == a.Length + b.Length
  {
    c_arr[i] := a[i];
    i := i + 1;
  }

  // Copy elements from array 'b' to 'c_arr'
  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant forall k :: 0 <= k < a.Length ==> c_arr[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c_arr[k + a.Length] == b[k]
    invariant c_arr.Length == a.Length + b.Length
  {
    c_arr[j + a.Length] := b[j];
    j := j + 1;
  }

  return c_arr;
}
// </vc-code>

