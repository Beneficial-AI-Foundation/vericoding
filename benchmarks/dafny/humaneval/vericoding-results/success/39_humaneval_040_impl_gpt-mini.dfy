// <vc-preamble>

predicate HasTripleSumToZero(l: seq<int>)
{
    exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>
lemma TripleWitness(l: seq<int>, a:int, b:int, c:int)
  requires 0 <= a < b < c < |l|
  requires l[a] + l[b] + l[c] == 0
  ensures HasTripleSumToZero(l)
{
  assert exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0;
}
// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasTripleSumToZero(l)
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  var i := 0;
  while i <= n - 3
    invariant 0 <= i <= n
    invariant forall a, b, c :: 0 <= a < b < c < n && a < i ==> l[a] + l[b] + l[c] != 0
  {
    var j := i + 1;
    while j <= n - 2
      invariant i + 1 <= j <= n
      invariant forall a, b, c :: 0 <= a < b < c < n && (a < i || (a == i && b < j)) ==> l[a] + l[b] + l[c] != 0
    {
      var k := j + 1;
      while k <= n - 1
        invariant j + 1 <= k <= n
        invariant forall a, b, c :: 0 <= a < b < c < n && (a < i || (a == i && b < j) || (a == i && b == j && c < k)) ==> l[a] + l[b] + l[c] != 0
      {
        if l[i] + l[j] + l[k] == 0 {
          result := true;
          assert exists a, b, c :: 0 <= a < b < c < n && l[a] + l[b] + l[c] == 0;
          return;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
