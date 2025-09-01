function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var a := new int[|s|];
  var idx := 0;
  while idx < |s|
    invariant 0 <= idx <= |s|
    invariant forall k :: 0 <= k < idx ==> a[k] == s[k]
  {
    a[idx] := s[idx];
    idx := idx + 1;
  }

  // Insertion sort
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant (forall j, k :: 0 <= j < k < i ==> digits_sum(a[j]) <= digits_sum(a[k]) ||
                                  (digits_sum(a[j]) == digits_sum(a[k]) && j < k))
    invariant multiset(a[0..i]) == multiset(s[0..i])
    invariant multiset(a[..]) == multiset(s)
    decreases a.Length - i
  {
    var key := a[i];
    var j := i - 1;
    while 0 <= j && digits_sum(a[j]) > digits_sum(key)
      invariant -1 <= j < i
      invariant forall p :: j < p < i ==> digits_sum(a[p]) > digits_sum(key)
      invariant multiset(a[0..i+1]) == multiset(s[0..i+1])
      invariant a[i] == old(a)[i]
      invariant forall p :: 0 <= p < j+1 ==> a[p] == old(a)[p]
      invariant forall p :: j+1 <= p < i ==> a[p] == old(a)[p-1]
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    a[j+1] := key;
    i := i + 1;
  }

  var result := [];
  var k := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant |result| == k
    invariant forall m :: 0 <= m < k ==> result[m] == a[m]
  {
    result := result + [a[k]];
    k := k + 1;
  }
  sorted := result;
}
// </vc-code>

