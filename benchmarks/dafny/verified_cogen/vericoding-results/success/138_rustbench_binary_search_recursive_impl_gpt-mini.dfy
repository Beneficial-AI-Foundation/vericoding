// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove prefix up to mid is <= elem using a loop */
lemma LeftPrefixLE(v: array<int>, c: int, f: int, mid: int, elem: int)
  requires 0 <= c <= mid <= f < v.Length
  requires forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
  requires v[mid] <= elem
  ensures forall k :: 0 <= k < mid + 1 ==> v[k] <= elem
{
  var i := 0;
  while i < mid + 1
    invariant 0 <= i <= mid + 1
    invariant forall j :: 0 <= j < i ==> v[j] <= elem
    decreases mid + 1 - i
  {
    if i < mid {
      assert v[i] <= v[mid];
    }
    assert v[mid] <= elem;
    assert v[i] <= elem;
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 3): prove suffix from mid is > elem using a loop */
lemma RightSuffixGT(v: array<int>, c: int, f: int, mid: int, elem: int)
  requires 0 <= c <= mid <= f < v.Length
  requires forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
  requires forall k :: f < k < v.Length ==> v[k] > elem
  requires v[mid] > elem
  ensures forall k :: mid <= k < v.Length ==> v[k] > elem
{
  var i := mid;
  while i < v.Length
    invariant mid <= i <= v.Length
    invariant forall j :: mid <= j < i ==> v[j] > elem
    decreases v.Length - i
  {
    if mid < i {
      assert v[mid] <= v[i];
    }
    assert v[mid] > elem;
    assert v[i] > elem;
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method BinarySearchRecursive(v: array<int>, elem: int, c: int, f: int) returns (p: int)
    requires v.Length <= 100000
    requires forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
    requires 0 <= c <= f + 1 <= v.Length
    requires forall k :: 0 <= k < c ==> v[k] <= elem
    requires forall k :: f < k < v.Length ==> v[k] > elem
    ensures -1 <= p < v.Length
    ensures forall u :: 0 <= u <= p ==> v[u] <= elem
    ensures forall w :: p < w < v.Length ==> v[w] > elem
    decreases f - c + 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): base case and recursive search using lemmas to establish preconditions */
  if (c > f) {
    p := c - 1;
  } else {
    var mid := c + (f - c) / 2;
    if v[mid] <= elem {
      LeftPrefixLE(v, c, f, mid, elem);
      p := BinarySearchRecursive(v, elem, mid + 1, f);
    } else {
      RightSuffixGT(v, c, f, mid, elem);
      p := BinarySearchRecursive(v, elem, c, mid - 1);
    }
  }
}
// </vc-code>
